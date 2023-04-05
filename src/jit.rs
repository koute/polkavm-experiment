use crate::isa::{BranchKind, Inst, LoadKind, Reg, RegImmKind, RegRegKind, ShiftKind, StoreKind};
use core::ops::ControlFlow;
use std::sync::Arc;

pub struct InstanceRef {
    memory: *mut u8,
    accessible_length: usize,
}

impl InstanceRef {
    pub fn regs(&self) -> &[u32] {
        unsafe { core::slice::from_raw_parts(self.memory.cast::<u32>().sub(32), 32) }
    }

    pub fn get_reg(&self, reg: Reg) -> u32 {
        let regs = unsafe { core::slice::from_raw_parts(self.memory.cast::<u32>().sub(32), 32) };

        regs[reg as usize]
    }

    pub fn set_reg(&mut self, reg: Reg, value: u32) {
        let regs = unsafe { core::slice::from_raw_parts_mut(self.memory.cast::<u32>().sub(32), 32) };

        regs[reg as usize] = value;
    }

    pub fn memory(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.memory, self.accessible_length) }
    }

    pub fn memory_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.memory, self.accessible_length) }
    }
}

pub trait UserContext {
    fn on_ecall(&mut self, _instance: &mut InstanceRef) -> ControlFlow<()>;
    fn on_unimp(&mut self, _instance: &mut InstanceRef) {}
    fn on_step(&mut self, _instance: &mut InstanceRef, _pc: u32) {}
}

impl UserContext for () {
    fn on_ecall(&mut self, _instance: &mut InstanceRef) -> ControlFlow<()> {
        ControlFlow::Break(())
    }
}

pub struct ModuleState<T> {
    pointer_code: *mut core::ffi::c_void,
    code_size: usize,
    data_size: usize,
    data_size_accessible: usize,
    data: Vec<u8>,
    labels: Vec<u64>,

    phantom: core::marker::PhantomData<T>,

    memory_prologue_size: usize,
    heap_size: usize,
}

impl<T> Drop for ModuleState<T> {
    fn drop(&mut self) {
        unsafe { nix::sys::mman::munmap(self.pointer_code, self.code_size).unwrap() }
    }
}

pub struct Module<T>(Arc<ModuleState<T>>);

pub struct Instance<T> {
    module: Arc<ModuleState<T>>,
    pointer_data: *mut core::ffi::c_void,
    // user: Box<T>
}

impl<T> Drop for Instance<T> {
    fn drop(&mut self) {
        unsafe { nix::sys::mman::munmap(self.pointer_data, self.module.data_size).unwrap() }
    }
}

pub struct Program<'a> {
    data: &'a [u8],
    opcodes: Vec<(u32, Inst)>,
}

impl<'a> Program<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        let elf = goblin::elf::Elf::parse(&data).unwrap();
        let text_section = elf
            .section_headers
            .iter()
            .find(|sec| {
                elf.shdr_strtab
                    .get_at(sec.sh_name)
                    .map(|name| name == ".text")
                    .unwrap_or(false)
            })
            .unwrap();

        let text =
            &data[text_section.sh_offset as usize..text_section.sh_offset as usize + text_section.sh_size as usize];
        let text = unsafe { std::slice::from_raw_parts(text.as_ptr().cast::<u32>(), text.len() / 4) };
        let mut opcodes = Vec::new();
        for (nth, &op) in text.iter().enumerate() {
            let pc = nth as u32 * 4;
            if let Some(op) = Inst::decode(op, pc) {
                match op {
                    Inst::JumpAndLinkRegister {
                        dst: ra_dst,
                        base,
                        value,
                    } => {
                        if let Some((
                            last_pc,
                            Inst::AddUpperImmediateToPc {
                                dst: base_upper,
                                value: value_upper,
                            },
                        )) = opcodes.last().copied()
                        {
                            if last_pc + 4 == pc && base == ra_dst && base == base_upper {
                                let value_upper = last_pc as i32 + value_upper as i32;
                                let target = (value_upper + value as i32) as u32 & !1;
                                opcodes.push((pc, Inst::JumpAndLink { dst: ra_dst, target }));

                                continue;
                            }
                        }
                    }
                    _ => {}
                }
                opcodes.push((pc, op));
            }
        }

        let data = &data[0x1000..];

        Program { data, opcodes }
    }
}

pub struct CompileConfig {
    enable_step: bool,
    memory_size: usize,
}

impl Default for CompileConfig {
    fn default() -> Self {
        Self {
            enable_step: false,
            memory_size: 2 * 1024 * 1024,
        }
    }
}

impl CompileConfig {
    /// When enabled the [`UserContext::on_step`] will be called while the program's executing.
    ///
    /// This is EXTREMELY SLOW and should be only used for debugging.
    pub fn enable_step(&mut self, enable: bool) {
        self.enable_step = enable;
    }

    pub fn set_memory_size(&mut self, size: usize) {
        self.memory_size = size;
    }
}

impl<T> Module<T> {
    pub fn compile(program: &Program, config: CompileConfig) -> Self
    where
        T: UserContext,
    {
        let label_count = program.opcodes.last().unwrap().0 as usize / 4 + 1;
        let heap_size = config.memory_size;
        let memory_prologue_size = 32 * 4 + label_count * 8;

        let data = program.data;
        let data_size_accessible = data.len() + heap_size;
        let data_size = align_to_next_page(memory_prologue_size + data_size_accessible + 8);

        let mut code = Vec::new();
        let mut branches = Vec::new();

        let mut labels = Vec::new();
        let mut current_rip = 0;

        labels.resize(label_count, 0);

        use iced_x86::code_asm::*;
        let mut asm = CodeAssembler::new(64).unwrap();

        macro_rules! update_code {
            () => {
                let instructions = asm.take_instructions();
                if !instructions.is_empty() {
                    let block = iced_x86::InstructionBlock::new(&instructions, 0);
                    let chunk = iced_x86::BlockEncoder::encode(64, block, 0).unwrap().code_buffer;
                    current_rip += chunk.len() as u64;
                    code.extend(chunk);
                }
            };
        }

        #[derive(Copy, Clone, PartialEq, Eq)]
        struct R {
            r64: iced_x86::code_asm::AsmRegister64,
            r32: iced_x86::code_asm::AsmRegister32,
            r16: iced_x86::code_asm::AsmRegister16,
            r8: iced_x86::code_asm::AsmRegister8,
        }

        impl R {
            fn r64(self) -> iced_x86::code_asm::AsmRegister64 {
                self.r64
            }
            fn r32(self) -> iced_x86::code_asm::AsmRegister32 {
                self.r32
            }
            fn r16(self) -> iced_x86::code_asm::AsmRegister16 {
                self.r16
            }
            fn r8(self) -> iced_x86::code_asm::AsmRegister8 {
                self.r8
            }
        }

        const RAX: R = R {
            r64: rax,
            r32: eax,
            r16: ax,
            r8: al,
        };

        const RBX: R = R {
            r64: rbx,
            r32: ebx,
            r16: bx,
            r8: bl,
        };

        const RCX: R = R {
            r64: rcx,
            r32: ecx,
            r16: cx,
            r8: cl,
        };

        const RDX: R = R {
            r64: rdx,
            r32: edx,
            r16: dx,
            r8: dl,
        };

        const RSI: R = R {
            r64: rsi,
            r32: esi,
            r16: si,
            r8: sil,
        };

        const RDI: R = R {
            r64: rdi,
            r32: edi,
            r16: di,
            r8: dil,
        };

        const RBP: R = R {
            r64: rbp,
            r32: ebp,
            r16: bp,
            r8: bpl,
        };

        #[allow(dead_code)]
        const RSP: R = R {
            r64: rsp,
            r32: esp,
            r16: sp,
            r8: spl,
        };

        const R8: R = R {
            r64: r8,
            r32: r8d,
            r16: r8w,
            r8: r8b,
        };

        const R9: R = R {
            r64: r9,
            r32: r9d,
            r16: r9w,
            r8: r9b,
        };

        const R10: R = R {
            r64: r10,
            r32: r10d,
            r16: r10w,
            r8: r10b,
        };

        const R11: R = R {
            r64: r11,
            r32: r11d,
            r16: r11w,
            r8: r11b,
        };

        const R12: R = R {
            r64: r12,
            r32: r12d,
            r16: r12w,
            r8: r12b,
        };

        const R13: R = R {
            r64: r13,
            r32: r13d,
            r16: r13w,
            r8: r13b,
        };

        const R14: R = R {
            r64: r14,
            r32: r14d,
            r16: r14w,
            r8: r14b,
        };

        macro_rules! reg_in_mem {
            ($reg: ident) => {
                r15 + (($reg as i64 - 32) * 4)
            };
        }

        macro_rules! native_reg {
            ($reg:ident) => {
                match $reg {
                    Reg::A0 => Some(RSI),
                    Reg::A1 => Some(RDI),
                    Reg::A2 => Some(R8),
                    Reg::SP => Some(R9),
                    Reg::S1 => Some(R10),
                    Reg::A3 => Some(R11),
                    Reg::S0 => Some(R12),
                    Reg::A4 => Some(R13),
                    Reg::RA => Some(R14),
                    Reg::A5 => Some(RBP),
                    Reg::T0 => Some(RAX),
                    Reg::T1 => Some(RBX),
                    Reg::T2 => Some(RDX),
                    _ => None,
                }
            };
        }

        macro_rules! is_reg_native {
            ($reg:ident) => {
                native_reg!($reg).is_some()
            };
        }

        macro_rules! swap_native_out {
            () => {
                for n in 0..32 {
                    let reg = Reg::decode(n);
                    if let Some(r) = native_reg!(reg) {
                        asm.push(r.r64()).unwrap();
                        asm.mov(r.r32(), dword_ptr(reg_in_mem!(reg))).unwrap();
                    }
                }

                update_code!();
            };
        }

        macro_rules! swap_native_in {
            () => {
                for n in (0..32).rev() {
                    let reg = Reg::decode(n);
                    if let Some(r) = native_reg!(reg) {
                        asm.mov(dword_ptr(reg_in_mem!(reg)), r.r32()).unwrap();
                        asm.pop(r.r64()).unwrap();
                    }
                }
            };
        }

        // Save registers.
        asm.push(rbp).unwrap();
        asm.push(rbx).unwrap();
        asm.push(r12).unwrap();
        asm.push(r13).unwrap();
        asm.push(r14).unwrap();
        asm.push(r15).unwrap();
        // Move the pointer to the vmctx into a pinned register.
        asm.mov(r15, rdi).unwrap();
        // Make sure the stack's 16-byte aligned.
        asm.sub(rsp, 8).unwrap();
        swap_native_out!();
        update_code!();

        let mut last_code_print = 0;
        let mut last_code_print_rip = 0;
        print_code(last_code_print_rip, &code[last_code_print..]);
        last_code_print = code.len();
        last_code_print_rip = current_rip;

        extern "C" fn on_ecall<T>(memory: *mut u8, accessible_length: usize) -> i64
        where
            T: UserContext,
        {
            unsafe {
                let userptr = *memory.add(accessible_length as usize).cast::<*mut T>();
                let user = &mut *userptr;
                let mut instance_ref = InstanceRef {
                    memory,
                    accessible_length,
                };
                let result = user.on_ecall(&mut instance_ref) == ControlFlow::Continue(());
                result as i64
            }
        }

        extern "C" fn on_unimp<T>(memory: *mut u8, accessible_length: usize)
        where
            T: UserContext,
        {
            unsafe {
                let userptr = *memory.add(accessible_length as usize).cast::<*mut T>();
                let user = &mut *userptr;
                let mut instance_ref = InstanceRef {
                    memory,
                    accessible_length,
                };
                user.on_unimp(&mut instance_ref);
            }
        }

        extern "C" fn on_step<T>(memory: *mut u8, accessible_length: usize, pc: u32)
        where
            T: UserContext,
        {
            unsafe {
                let userptr = *memory.add(accessible_length as usize).cast::<*mut T>();
                let user = &mut *userptr;
                let mut instance_ref = InstanceRef {
                    memory,
                    accessible_length,
                };
                user.on_step(&mut instance_ref, pc);
            }
        }

        const TARGET_EXIT: u32 = u32::MAX;
        const TARGET_UNIMP: u32 = u32::MAX - 1;

        for &(pc, op) in &program.opcodes {
            log::trace!("{:04x}: {:?}", pc, op);
            labels[(pc / 4) as usize] = current_rip;

            #[derive(Default)]
            struct UsedRegs {
                rax: bool,
                rbx: bool,
                rcx: bool,
                rdx: bool,
                rsi: bool,
                rdi: bool,
            }

            let mut used_regs = UsedRegs {
                rax: false,
                rbx: false,
                rdx: false,
                rcx: false,
                rsi: false,
                rdi: false,
            };

            for n in 0..32 {
                let reg = Reg::decode(n);
                if let Some(r) = native_reg!(reg) {
                    if r.r64() == rax {
                        used_regs.rax = true;
                    } else if r.r64() == rdx {
                        used_regs.rdx = true;
                    } else if r.r64() == rcx {
                        used_regs.rcx = true;
                    } else if r.r64() == rsi {
                        used_regs.rsi = true;
                    } else if r.r64() == rdi {
                        used_regs.rdi = true;
                    } else if r.r64() == rbx {
                        used_regs.rbx = true;
                    }
                }
            }

            macro_rules! release_reg {
                ($reg:expr) => {
                    if $reg == RDX {
                        used_regs.rdx = false;
                    } else if $reg == RCX {
                        used_regs.rcx = false;
                    } else {
                        unreachable!()
                    }
                };
            }

            macro_rules! next_scratch_reg {
                () => {
                    if !used_regs.rdx {
                        #[allow(unused_assignments)]
                        {
                            used_regs.rdx = true;
                        }
                        RDX
                    } else if !used_regs.rcx {
                        #[allow(unused_assignments)]
                        {
                            used_regs.rcx = true;
                        }
                        RCX
                    } else if !used_regs.rsi {
                        #[allow(unused_assignments)]
                        {
                            used_regs.rsi = true;
                        }
                        RSI
                    } else if !used_regs.rax {
                        #[allow(unused_assignments)]
                        {
                            used_regs.rax = true;
                        }
                        RAX
                    } else if !used_regs.rdi {
                        #[allow(unused_assignments)]
                        {
                            used_regs.rdi = true;
                        }
                        RDI
                    } else if !used_regs.rbx {
                        #[allow(unused_assignments)]
                        {
                            used_regs.rbx = true;
                        }
                        RBX
                    } else {
                        unreachable!("ran out of temporary registers")
                    }
                };
            }

            macro_rules! get_reg {
                ($reg:ident: ecx) => {{
                    if !used_regs.rcx {
                        used_regs.rcx = true;
                        if let Some(r) = native_reg!($reg) {
                            asm.mov(ecx, r.r32()).unwrap();
                        } else {
                            asm.mov(ecx, dword_ptr(reg_in_mem!($reg))).unwrap();
                        }
                        update_code!();
                    } else {
                        todo!()
                    }
                    RCX
                }};

                ($reg:ident) => {{
                    if $reg != Reg::Zero {
                        if let Some(r) = native_reg!($reg) {
                            r
                        } else {
                            let r = next_scratch_reg!();
                            asm.mov(r.r32, dword_ptr(reg_in_mem!($reg))).unwrap();
                            update_code!();
                            r
                        }
                    } else {
                        let r = next_scratch_reg!();
                        asm.xor(r.r64, r.r64).unwrap();
                        update_code!();
                        r
                    }
                }};
            }

            macro_rules! get_reg_scratch {
                ($reg:ident) => {
                    if let Some(r) = native_reg!($reg) {
                        let reg = next_scratch_reg!();
                        asm.mov(reg.r64(), r.r64()).unwrap();
                        update_code!();
                        reg
                    } else {
                        get_reg!($reg)
                    }
                };
            }

            macro_rules! get_set_reg {
                ($dst:ident = $src:ident => $code:block) => {{
                    if $dst == $src {
                        if let Some(r) = native_reg!($dst) {
                            #[allow(unused_variables)]
                            let $dst = r;
                            $code;
                        } else {
                            let reg = get_reg!($dst);
                            {
                                #[allow(unused_variables)]
                                let $dst = reg;
                                #[allow(unused_variables)]
                                let $src = ();
                                $code;
                            }

                            if $dst != Reg::Zero {
                                asm.mov(dword_ptr(reg_in_mem!($dst)), reg.r32()).unwrap();
                            }
                        }
                    } else {
                        if let Some(r_dst) = native_reg!($dst) {
                            let $dst = r_dst;

                            if $src != Reg::Zero {
                                if let Some(r_src) = native_reg!($src) {
                                    asm.mov($dst.r64(), r_src.r64()).unwrap();
                                } else {
                                    asm.mov($dst.r32(), byte_ptr(reg_in_mem!($src))).unwrap();
                                }
                            }

                            #[allow(unused_variables)]
                            let $src = ();
                            $code;
                        } else {
                            let dst = next_scratch_reg!();

                            if $src != Reg::Zero {
                                if let Some(r_src) = native_reg!($src) {
                                    asm.mov(dst.r32(), r_src.r32()).unwrap();
                                } else {
                                    asm.mov(dst.r32(), byte_ptr(reg_in_mem!($src))).unwrap();
                                }
                            }

                            {
                                #[allow(unused_variables)]
                                let $dst = dst;
                                #[allow(unused_variables)]
                                let $src = ();
                                $code;
                            }

                            if $dst != Reg::Zero {
                                asm.mov(dword_ptr(reg_in_mem!($dst)), dst.r32()).unwrap();
                            }
                        }
                    }

                    update_code!();
                }};
            }

            macro_rules! set_reg {
                ($reg:ident => $code:block) => {{
                    if let Some(r) = native_reg!($reg) {
                        {
                            let $reg = r;
                            $code;
                        }
                        update_code!();
                    } else {
                        let reg = next_scratch_reg!();

                        {
                            let $reg = reg;
                            $code;
                        }

                        if $reg != Reg::Zero {
                            asm.mov(dword_ptr(reg_in_mem!($reg)), reg.r32()).unwrap();
                        }
                        update_code!();
                    }
                }};
            }

            if config.enable_step {
                swap_native_in!();
                asm.mov(rdi, r15).unwrap();
                asm.mov(rsi, data_size_accessible as u64).unwrap();
                asm.mov(edx, pc).unwrap();
                asm.mov(rax, on_step::<T> as u64).unwrap();
                asm.call(rax).unwrap();
                swap_native_out!();
            }

            match op {
                Inst::AddUpperImmediateToPc { dst, value } => {
                    let value = (pc as i32 + value as i32) as u32;
                    set_reg! { dst => {
                        asm.mov(dst.r32(), value).unwrap();
                    }};
                }
                Inst::JumpAndLinkRegister { dst, base, value } => {
                    let base = get_reg_scratch!(base);
                    let base64 = base.r64();
                    let base32 = base.r32();
                    if value != 0 {
                        asm.add(base64, value as i32).unwrap();
                    }

                    asm.and(base32, 0xfffffffe_u32).unwrap();
                    asm.shl(base64, 1).unwrap(); // Every label takes 8 bytes.
                    asm.add(base64, r15).unwrap();
                    asm.sub(base64, 32 * 4 + label_count as i32 * 8).unwrap();

                    // NOTE: This must be before the jump since 'dst' can be equal to 'base'.
                    if dst != Reg::Zero {
                        set_reg! { dst => {
                            asm.mov(dst.r32(), (pc as u32).wrapping_add(4)).unwrap();
                        }}
                    }
                    asm.jmp(qword_ptr(base64)).unwrap();

                    update_code!();
                }
                Inst::Ecall => {
                    swap_native_in!();
                    asm.mov(rdi, r15).unwrap();
                    asm.mov(rsi, data_size_accessible as u64).unwrap();
                    asm.mov(rax, on_ecall::<T> as u64).unwrap();
                    asm.call(rax).unwrap();
                    asm.cmp(rax, 0).unwrap();
                    update_code!();
                    branches.push((code.len(), current_rip, TARGET_EXIT, iced_x86::Code::Je_rel32_64));
                    for _ in 0..6 {
                        asm.nop().unwrap();
                    }
                    update_code!();
                    swap_native_out!();
                }
                Inst::Unimplemented => {
                    update_code!();
                    assert!(asm.instructions().is_empty());
                    branches.push((code.len(), current_rip, TARGET_UNIMP, iced_x86::Code::Jmp_rel32_64));
                    for _ in 0..5 {
                        asm.nop().unwrap();
                    }

                    update_code!();
                }
                Inst::JumpAndLink { dst, target } => {
                    if dst != Reg::Zero {
                        set_reg! { dst => {
                            asm.mov(dst.r32(), (pc as u32).wrapping_add(4)).unwrap();
                        }}

                        update_code!();
                    }

                    update_code!();
                    assert!(asm.instructions().is_empty());
                    branches.push((code.len(), current_rip, target, iced_x86::Code::Jmp_rel32_64));
                    for _ in 0..5 {
                        asm.nop().unwrap();
                    }

                    update_code!();
                }
                Inst::Branch {
                    kind,
                    src1,
                    src2,
                    target,
                } => {
                    macro_rules! branch {
                        ($kind:ident) => {{
                            assert!(asm.instructions().is_empty());
                            branches.push((code.len(), current_rip, target, $kind));
                            for _ in 0..6 {
                                asm.nop().unwrap();
                            }

                            update_code!();
                        }};
                    }

                    let mut invert = false;
                    if src1 == Reg::Zero {
                        let r_src2 = get_reg!(src2);
                        asm.cmp(r_src2.r32(), 0).unwrap();
                        invert = true;
                    } else if src2 == Reg::Zero {
                        let r_src1 = get_reg!(src1);
                        asm.cmp(r_src1.r32(), 0).unwrap();
                    } else {
                        let r_src1 = get_reg!(src1);
                        let r_src2 = get_reg!(src2);
                        asm.cmp(r_src1.r32(), r_src2.r32()).unwrap();
                    }

                    update_code!();

                    use iced_x86::Code::*;
                    let kind = match kind {
                        BranchKind::Eq => Je_rel32_64,
                        BranchKind::NotEq => Jne_rel32_64,
                        BranchKind::LessSigned => {
                            if !invert {
                                Jl_rel32_64
                            } else {
                                Jge_rel32_64
                            }
                        }
                        BranchKind::GreaterOrEqualSigned => {
                            if !invert {
                                Jge_rel32_64
                            } else {
                                Jl_rel32_64
                            }
                        }
                        BranchKind::LessUnsigned => {
                            if !invert {
                                Jb_rel32_64
                            } else {
                                Jae_rel32_64
                            }
                        }
                        BranchKind::GreaterOrEqualUnsigned => {
                            if !invert {
                                Jae_rel32_64
                            } else {
                                Jb_rel32_64
                            }
                        }
                    };

                    branch!(kind)
                }
                Inst::Load {
                    kind,
                    dst,
                    base,
                    offset,
                } => {
                    let offset = offset as i64;
                    let base = if base != Reg::Zero {
                        let base = get_reg_scratch!(base).r64();
                        asm.add(base, r15).unwrap();
                        base
                    } else {
                        r15
                    };

                    match kind {
                        LoadKind::I8 => {
                            set_reg! { dst => {
                                asm.movsx(dst.r32(), byte_ptr(base + offset)).unwrap();
                            }};
                        }
                        LoadKind::I16 => {
                            set_reg! { dst => {
                                asm.movsx(dst.r32(), word_ptr(base + offset)).unwrap();
                            }};
                        }
                        LoadKind::U32 => {
                            set_reg! { dst => {
                                asm.mov(dst.r32(), dword_ptr(base + offset)).unwrap();
                            }}
                        }
                        LoadKind::U8 => {
                            set_reg! { dst => {
                                asm.movzx(dst.r32(), byte_ptr(base + offset)).unwrap();
                            }};
                        }
                        LoadKind::U16 => {
                            set_reg! { dst => {
                                asm.movzx(dst.r32(), word_ptr(base + offset)).unwrap();
                            }};
                        }
                    }
                }
                Inst::Store {
                    kind,
                    src,
                    base,
                    offset,
                } => {
                    let offset = offset as i64;
                    let base = if base != Reg::Zero {
                        let base = get_reg_scratch!(base).r64();
                        asm.add(base, r15).unwrap();
                        base
                    } else {
                        r15
                    };

                    if src != Reg::Zero {
                        match kind {
                            StoreKind::U8 => {
                                let src = get_reg!(src);
                                asm.mov(byte_ptr(base + offset), src.r8()).unwrap();
                            }
                            StoreKind::U16 => {
                                let src = get_reg!(src);
                                asm.mov(word_ptr(base + offset), src.r16()).unwrap();
                            }
                            StoreKind::U32 => {
                                let src = get_reg!(src);
                                asm.mov(dword_ptr(base + offset), src.r32()).unwrap();
                            }
                        }
                    } else {
                        match kind {
                            StoreKind::U8 => {
                                asm.mov(byte_ptr(base + offset), 0).unwrap();
                            }
                            StoreKind::U16 => {
                                asm.mov(word_ptr(base + offset), 0).unwrap();
                            }
                            StoreKind::U32 => {
                                asm.mov(dword_ptr(base + offset), 0).unwrap();
                            }
                        }
                    }

                    update_code!();
                }
                Inst::LoadUpperImmediate { dst: Reg::Zero, .. }
                | Inst::RegImm { dst: Reg::Zero, .. }
                | Inst::RegReg { dst: Reg::Zero, .. }
                | Inst::Shift { dst: Reg::Zero, .. } => {
                    asm.nop().unwrap();
                    update_code!();
                }
                Inst::LoadUpperImmediate { dst, value } => {
                    set_reg! { dst => {
                        asm.mov(dst.r32(), value).unwrap();
                    }};
                }
                Inst::RegImm {
                    kind: RegImmKind::Add,
                    dst,
                    src: Reg::Zero,
                    imm,
                } => {
                    if is_reg_native!(dst) {
                        if imm == 0 {
                            set_reg! { dst => {
                                asm.xor(dst.r32(), dst.r32()).unwrap();
                            }};
                        } else {
                            set_reg! { dst => {
                                asm.mov(dst.r32(), imm).unwrap();
                            }};
                        }
                    } else {
                        asm.mov(dword_ptr(reg_in_mem!(dst)), imm as u32).unwrap();
                        update_code!();
                    }
                }
                Inst::RegImm {
                    kind: RegImmKind::Add,
                    dst,
                    src,
                    imm: 0,
                } => {
                    get_set_reg!( dst = src => {} );
                }
                Inst::RegImm { kind, dst, src, imm } => match kind {
                    RegImmKind::Add => {
                        let src = get_reg!(src);
                        set_reg! { dst => {
                            asm.lea(dst.r32(), dword_ptr(src.r32() + imm)).unwrap();
                        }};
                    }
                    RegImmKind::SetLessThanSigned => {
                        let tmp = next_scratch_reg!();
                        let src = get_reg!(src);
                        set_reg! { dst => {
                            asm.xor(tmp.r32(), tmp.r32()).unwrap();
                            asm.cmp(src.r32(), imm).unwrap();
                            asm.setl(tmp.r8()).unwrap();
                            asm.mov(dst.r32(), tmp.r32()).unwrap();
                        }};
                    }
                    RegImmKind::SetLessThanUnsigned => {
                        let tmp = next_scratch_reg!();
                        let src = get_reg!(src);
                        set_reg! { dst => {
                            asm.xor(tmp.r32(), tmp.r32()).unwrap();
                            asm.cmp(src.r32(), imm).unwrap();
                            asm.setb(tmp.r8()).unwrap();
                            asm.mov(dst.r32(), tmp.r32()).unwrap();
                        }};
                    }
                    RegImmKind::Xor => {
                        get_set_reg!( dst = src => {
                            asm.xor(dst.r32(), imm).unwrap();
                        });
                    }
                    RegImmKind::Or => {
                        get_set_reg!( dst = src => {
                            asm.or(dst.r32(), imm).unwrap();
                        });
                    }
                    RegImmKind::And => {
                        get_set_reg!( dst = src => {
                            asm.and(dst.r32(), imm).unwrap();
                        });
                    }
                },
                Inst::Shift { kind, dst, src, amount } => match kind {
                    ShiftKind::LogicalLeft => {
                        get_set_reg!( dst = src => {
                            asm.shl(dst.r32(), amount as u32).unwrap();
                        });
                    }
                    ShiftKind::LogicalRight => {
                        get_set_reg!( dst = src => {
                            asm.shr(dst.r32(), amount as u32).unwrap();
                        });
                    }
                    ShiftKind::ArithmeticRight => {
                        get_set_reg!( dst = src => {
                            asm.sar(dst.r32(), amount as u32).unwrap();
                        });
                    }
                },
                Inst::RegReg {
                    kind: RegRegKind::SetLessThanSigned | RegRegKind::SetLessThanUnsigned,
                    dst,
                    src1,
                    src2,
                } if src1 == src2 => {
                    set_reg! { dst => {
                        asm.xor(dst.r32(), dst.r32()).unwrap();
                    }};
                }
                Inst::RegReg { kind, dst, src1, src2 }
                    if kind == RegRegKind::SetLessThanSigned || kind == RegRegKind::SetLessThanUnsigned =>
                {
                    if src1 == Reg::Zero {
                        let r_src2 = get_reg!(src2);
                        if kind == RegRegKind::SetLessThanSigned {
                            asm.cmp(r_src2.r32(), 0).unwrap();
                            set_reg! { dst => {
                                asm.setge(dst.r8()).unwrap();
                                asm.and(dst.r64(), 1).unwrap();
                            }};
                        } else {
                            assert_eq!(kind, RegRegKind::SetLessThanUnsigned);
                            asm.test(r_src2.r32(), r_src2.r32()).unwrap();
                            set_reg! { dst => {
                                asm.setne(dst.r8()).unwrap();
                                asm.and(dst.r64(), 1).unwrap();
                            }};
                        }
                    } else {
                        let r_src1 = get_reg!(src1);
                        let r_src2 = get_reg!(src2);

                        asm.cmp(r_src1.r32(), r_src2.r32()).unwrap();
                        if !is_reg_native!(src1) {
                            release_reg!(r_src1);
                        }

                        if !is_reg_native!(src2) {
                            release_reg!(r_src2);
                        }

                        set_reg! { dst => {
                            if kind == RegRegKind::SetLessThanSigned {
                                asm.setl(dst.r8()).unwrap();
                            } else {
                                assert_eq!(kind, RegRegKind::SetLessThanUnsigned);
                                asm.setb(dst.r8()).unwrap();
                            }
                            asm.and(dst.r64(), 1).unwrap();
                        }};
                    }

                    update_code!();
                }
                Inst::RegReg {
                    kind,
                    dst,
                    mut src1,
                    mut src2,
                } => {
                    if dst != src1 && dst == src2 {
                        if matches!(
                            kind,
                            RegRegKind::Add
                                | RegRegKind::Xor
                                | RegRegKind::Or
                                | RegRegKind::And
                                | RegRegKind::Mul
                                | RegRegKind::MulUpperSignedSigned
                                | RegRegKind::MulUpperUnsignedUnsigned
                        ) {
                            core::mem::swap(&mut src1, &mut src2);
                        }
                    }

                    let requires_ecx = matches!(
                        kind,
                        RegRegKind::ShiftLogicalLeft | RegRegKind::ShiftLogicalRight | RegRegKind::ShiftArithmeticRight
                    );

                    let (r_dst, r_src) = if dst == src1 && dst == src2 {
                        let r_dst = get_reg!(dst);
                        let r_src = r_dst;
                        (r_dst, r_src)
                    } else if dst == src1 {
                        let r_src = if requires_ecx {
                            assert!(!used_regs.rcx);
                            get_reg!(src2: ecx)
                        } else {
                            get_reg!(src2)
                        };

                        let r_dst = if let Some(r) = native_reg!(dst) {
                            r
                        } else {
                            let r = next_scratch_reg!();
                            asm.mov(r.r32(), dword_ptr(reg_in_mem!(src1))).unwrap();
                            r
                        };

                        (r_dst, r_src)
                    } else if dst == src2 {
                        let r_src = if requires_ecx {
                            assert!(!used_regs.rcx);
                            used_regs.rcx = true;
                            RCX
                        } else {
                            next_scratch_reg!()
                        };

                        let r_dst = get_reg!(dst);
                        asm.mov(r_src.r32(), r_dst.r32()).unwrap();

                        if let Some(r) = native_reg!(src1) {
                            asm.mov(r_dst.r32(), r.r32()).unwrap();
                        } else {
                            asm.mov(r_dst.r32(), dword_ptr(reg_in_mem!(src1))).unwrap();
                        }

                        (r_dst, r_src)
                    } else {
                        let r_src = if requires_ecx {
                            assert!(!used_regs.rcx);
                            get_reg!(src2: ecx)
                        } else {
                            get_reg!(src2)
                        };

                        let r_dst = if let Some(r) = native_reg!(dst) {
                            r
                        } else {
                            next_scratch_reg!()
                        };

                        if let Some(r) = native_reg!(src1) {
                            asm.mov(r_dst.r32(), r.r32()).unwrap();
                        } else {
                            asm.mov(r_dst.r32(), dword_ptr(reg_in_mem!(src1))).unwrap();
                        }

                        (r_dst, r_src)
                    };

                    match kind {
                        RegRegKind::Add => asm.add(r_dst.r32(), r_src.r32()).unwrap(),
                        RegRegKind::Sub => asm.sub(r_dst.r32(), r_src.r32()).unwrap(),
                        RegRegKind::Xor => asm.xor(r_dst.r32(), r_src.r32()).unwrap(),
                        RegRegKind::Or => asm.or(r_dst.r32(), r_src.r32()).unwrap(),
                        RegRegKind::And => asm.and(r_dst.r32(), r_src.r32()).unwrap(),
                        RegRegKind::ShiftLogicalLeft => {
                            assert_eq!(r_src.r32(), ecx);
                            asm.shl(r_dst.r32(), cl).unwrap();
                        }
                        RegRegKind::ShiftLogicalRight => {
                            assert_eq!(r_src.r32(), ecx);
                            asm.shr(r_dst.r32(), cl).unwrap();
                        }
                        RegRegKind::ShiftArithmeticRight => {
                            assert_eq!(r_src.r32(), ecx);
                            asm.sar(r_dst.r32(), cl).unwrap();
                        }
                        RegRegKind::SetLessThanSigned => unreachable!(),
                        RegRegKind::SetLessThanUnsigned => unreachable!(),
                        RegRegKind::Mul => {
                            asm.imul_2(r_dst.r32(), r_src.r32()).unwrap();
                        }
                        RegRegKind::MulUpperSignedSigned => {
                            // movsxd	rcx, edi
                            // movsxd	rax, esi
                            // imul	rax, rcx
                            // shr	rax, 32
                            todo!();
                        }
                        RegRegKind::MulUpperUnsignedUnsigned => {
                            // mov	ecx, edi
                            // mov	eax, esi
                            // imul	rax, rcx
                            // shr	rax, 32
                            todo!();
                        }
                        RegRegKind::MulUpperSignedUnsigned => {
                            // movsxd	rcx, edi
                            // mov	eax, esi
                            // imul	rax, rcx
                            // shr	rax, 32
                            let tmp1 = next_scratch_reg!();
                            let tmp2 = next_scratch_reg!();
                            asm.movsxd(tmp1.r64(), r_dst.r32()).unwrap();
                            asm.mov(tmp2.r32(), r_src.r32()).unwrap();
                            asm.imul_2(tmp2.r64(), tmp1.r64()).unwrap();
                            asm.shr(tmp2.r64(), 32).unwrap();
                            asm.mov(r_dst.r32(), tmp2.r32()).unwrap();
                        }
                        RegRegKind::Div => {
                            todo!();
                        }
                        RegRegKind::DivUnsigned => {
                            todo!();
                        }
                        RegRegKind::Rem => {
                            todo!();
                        }
                        RegRegKind::RemUnsigned => {
                            todo!();
                        }
                    };

                    if !is_reg_native!(dst) && dst != Reg::Zero {
                        asm.mov(dword_ptr(reg_in_mem!(dst)), r_dst.r32()).unwrap();
                    }

                    update_code!();
                }
            }

            assert!(asm.instructions().is_empty());

            print_code(last_code_print_rip, &code[last_code_print..]);
            last_code_print = code.len();
            last_code_print_rip = current_rip;
        }

        swap_native_in!();
        update_code!();

        let exit_rip = current_rip;
        asm.add(rsp, 8).unwrap();
        asm.pop(r15).unwrap();
        asm.pop(r14).unwrap();
        asm.pop(r13).unwrap();
        asm.pop(r12).unwrap();
        asm.pop(rbx).unwrap();
        asm.pop(rbp).unwrap();
        asm.ret().unwrap();
        update_code!();

        let unimp_rip = current_rip;
        swap_native_in!();
        update_code!();
        asm.mov(rdi, r15).unwrap();
        asm.mov(rsi, data_size_accessible as u64).unwrap();
        asm.mov(rax, on_unimp::<T> as u64).unwrap();
        asm.call(rax).unwrap();
        asm.add(rsp, 8).unwrap();
        asm.pop(r15).unwrap();
        asm.pop(r14).unwrap();
        asm.pop(r13).unwrap();
        asm.pop(r12).unwrap();
        asm.pop(rbx).unwrap();
        asm.pop(rbp).unwrap();
        asm.ret().unwrap();
        update_code!();

        print_code(last_code_print_rip, &code[last_code_print..]);
        #[allow(unused_assignments)]
        {
            last_code_print = code.len();
            last_code_print_rip = current_rip;
        }

        for (code_offset, current_rip, branch_target, branch_kind) in branches {
            let target_rip = if branch_target == TARGET_EXIT {
                exit_rip
            } else if branch_target == TARGET_UNIMP {
                unimp_rip
            } else {
                *labels.get((branch_target / 4) as usize).unwrap()
            };

            let chunk = encode_branch(branch_kind, current_rip, target_rip).unwrap();
            code[code_offset..code_offset + chunk.len()].copy_from_slice(&chunk);
        }

        log::trace!("Compilation finished!");

        let code_size = align_to_next_page(code.len());
        let pointer_code = unsafe {
            nix::sys::mman::mmap(
                None,
                code_size.try_into().unwrap(),
                nix::sys::mman::ProtFlags::PROT_READ | nix::sys::mman::ProtFlags::PROT_WRITE,
                nix::sys::mman::MapFlags::MAP_PRIVATE | nix::sys::mman::MapFlags::MAP_ANONYMOUS,
                -1,
                0,
            )
            .unwrap()
        };

        {
            let slice = unsafe { std::slice::from_raw_parts_mut(pointer_code.cast::<u8>(), code.len()) };
            slice.copy_from_slice(&code);
            std::mem::drop(code);

            print_code(pointer_code as u64, &slice);
        }

        unsafe {
            nix::sys::mman::mprotect(
                pointer_code,
                code_size,
                nix::sys::mman::ProtFlags::PROT_READ | nix::sys::mman::ProtFlags::PROT_EXEC,
            )
            .unwrap();
        }

        assert_eq!(labels.len(), label_count);
        for label in &mut labels {
            *label += pointer_code as u64;
        }

        Module(Arc::new(ModuleState {
            pointer_code,
            code_size,
            data_size,
            data_size_accessible,
            data: data.to_vec(),
            labels,
            phantom: std::marker::PhantomData,

            memory_prologue_size,
            heap_size,
        }))
    }

    pub fn instantiate(&self, userctx: T) -> Instance<T> {
        let pointer_data = unsafe {
            nix::sys::mman::mmap(
                None,
                self.0.data_size.try_into().unwrap(),
                nix::sys::mman::ProtFlags::PROT_READ | nix::sys::mman::ProtFlags::PROT_WRITE,
                nix::sys::mman::MapFlags::MAP_PRIVATE | nix::sys::mman::MapFlags::MAP_ANONYMOUS,
                -1,
                0,
            )
            .unwrap()
        };

        {
            let slice = unsafe { std::slice::from_raw_parts_mut(pointer_data.cast::<u8>(), self.0.data_size) };
            slice[self.0.memory_prologue_size..self.0.memory_prologue_size + self.0.data.len()]
                .copy_from_slice(&self.0.data);
        }

        {
            let regs = unsafe {
                std::slice::from_raw_parts_mut(pointer_data.cast::<u8>().add(self.0.labels.len() * 8).cast::<u32>(), 32)
            };
            regs[Reg::SP as usize] = (self.0.data.len() + self.0.heap_size) as u32;
        }

        {
            let labels_in_mem =
                unsafe { std::slice::from_raw_parts_mut(pointer_data.cast::<u64>(), self.0.labels.len()) };
            labels_in_mem.copy_from_slice(&self.0.labels);
        }

        let user = Box::new(userctx);

        unsafe {
            let userptr = Box::into_raw(user);
            core::ptr::write(
                pointer_data
                    .cast::<u8>()
                    .add(self.0.memory_prologue_size + self.0.data_size_accessible)
                    .cast::<*const T>(),
                userptr,
            );
        }

        Instance {
            module: self.0.clone(),
            pointer_data,
        }
    }
}

impl<T> Instance<T> {
    pub fn regs(&self) -> &[u32] {
        unsafe {
            std::slice::from_raw_parts(
                self.pointer_data
                    .cast::<u8>()
                    .add(self.module.labels.len() as usize * 8)
                    .cast::<u32>(),
                32,
            )
        }
    }

    pub fn regs_mut(&mut self) -> &mut [u32] {
        unsafe {
            std::slice::from_raw_parts_mut(
                self.pointer_data
                    .cast::<u8>()
                    .add(self.module.labels.len() as usize * 8)
                    .cast::<u32>(),
                32,
            )
        }
    }

    pub fn set_reg(&mut self, reg: Reg, value: u32) {
        let regs = self.regs_mut();
        regs[reg as usize] = value;
    }

    pub fn user(&self) -> &T {
        unsafe {
            &**self
                .pointer_data
                .cast::<u8>()
                .add(self.module.memory_prologue_size + self.module.data_size_accessible)
                .cast::<*const T>()
        }
    }

    pub fn user_mut(&mut self) -> &mut T {
        unsafe {
            &mut **self
                .pointer_data
                .cast::<u8>()
                .add(self.module.memory_prologue_size + self.module.data_size_accessible)
                .cast::<*mut T>()
        }
    }

    pub fn run(&mut self) {
        unsafe {
            let entry_point: extern "C" fn(usize) = core::mem::transmute(self.module.pointer_code);
            let p = self.pointer_data.cast::<u8>().add(self.module.memory_prologue_size) as usize;

            gdb_hook();
            entry_point(p);
        }
    }
}

// Just a dummy function to make it easier to set up a breakpoint with gdb.
#[inline(never)]
#[no_mangle]
extern "C" fn gdb_hook() {}

fn print_code(code_origin: u64, code: &[u8]) {
    use std::fmt::Write;

    if !log::log_enabled!(log::Level::Trace) {
        return;
    }

    let mut buffer = String::new();
    let mut decoder = iced_x86::Decoder::with_ip(64, &code, code_origin, iced_x86::DecoderOptions::NONE);
    let mut formatter = iced_x86::NasmFormatter::new();
    use iced_x86::Formatter;
    let mut output = String::new();
    while decoder.can_decode() {
        let mut instruction = iced_x86::Instruction::default();
        decoder.decode_out(&mut instruction);

        output.clear();
        formatter.format(&instruction, &mut output);

        write!(&mut buffer, "{:016X} ", instruction.ip()).unwrap();
        let start_index = (instruction.ip() - code_origin) as usize;
        let instr_bytes = &code[start_index..start_index + instruction.len()];
        for b in instr_bytes.iter() {
            write!(&mut buffer, "{:02X}", b).unwrap();
        }
        const HEXBYTES_COLUMN_BYTE_LENGTH: usize = 10;
        if instr_bytes.len() < HEXBYTES_COLUMN_BYTE_LENGTH {
            for _ in 0..HEXBYTES_COLUMN_BYTE_LENGTH - instr_bytes.len() {
                write!(&mut buffer, "  ").unwrap();
            }
        }
        writeln!(&mut buffer, " {}", output).unwrap();
    }

    log::trace!("\n{}", buffer);
}

fn align_to_next_page(value: usize) -> usize {
    let page_size = 4096;
    if value & page_size - 1 == 0 {
        value
    } else {
        (value + page_size) & !(page_size - 1)
    }
}

fn encode_branch(branch_kind: iced_x86::Code, current: u64, target: u64) -> Option<Vec<u8>> {
    // The branch instructions have two encodings:
    //   1) a two byte one from -128 to 127 (inclusive)
    //   2) a six byte one
    //
    // The jump's origin is *after* the branch instruction.
    //
    // So far example, if we're using the two byte encoding
    // and we'd like to have the branch jump to the next
    // instruction its offset would be 0 (encoded as '0x74 0x00').

    let offset = target as i64 - current as i64;
    if offset > 0x80000005 || offset < -0x7ffffffa {
        // Out of range for the six byte instruction.
        return None;
    }

    let instruction = iced_x86::Instruction::with_branch(branch_kind, offset as u64).unwrap();

    let instructions = &[instruction];
    let block = iced_x86::InstructionBlock::new(instructions, 0);
    let code = iced_x86::BlockEncoder::encode(64, block, 0).unwrap().code_buffer;
    if offset < -126 || offset > 129 {
        if branch_kind == iced_x86::Code::Jmp_rel32_64 {
            assert_eq!(code.len(), 5);
        } else {
            assert_eq!(code.len(), 6);
        }
    } else {
        assert_eq!(code.len(), 2);
    }

    Some(code)
}

#[test]
fn test_encode_branch() {
    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 0, 2).unwrap(),
        vec![0x74, 0x00]
    );
    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 1, 3).unwrap(),
        vec![0x74, 0x00]
    );

    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 0, 3).unwrap(),
        vec![0x74, 0x01]
    );
    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 0, 129).unwrap(),
        vec![0x74, 0x7f]
    );
    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 0, 130).unwrap(),
        vec![0x0F, 0x84, 130 - 6, 0, 0, 0]
    );

    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 126, 0).unwrap(),
        vec![0x74, 0x80]
    );
    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 125, 0).unwrap(),
        vec![0x74, 0x81]
    );

    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 127, 0).unwrap(),
        vec![0x0F, 0x84, 0x7b, 0xff, 0xff, 0xff]
    );

    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 0, 0x7FFFFFFF + 6).unwrap(),
        vec![0x0F, 0x84, 0xff, 0xff, 0xff, 0x7f]
    );

    assert_eq!(
        encode_branch(iced_x86::Code::Je_rel32_64, 0x7FFFFFFF - 5, 0).unwrap(),
        vec![0x0F, 0x84, 0, 0, 0, 0x80]
    );

    assert!(encode_branch(iced_x86::Code::Je_rel32_64, 0, 0x7FFFFFFF + 7).is_none());
    assert!(encode_branch(iced_x86::Code::Je_rel32_64, 0x7FFFFFFF - 4, 0).is_none());

    for n in 0..1000 {
        encode_branch(iced_x86::Code::Je_rel32_64, n, 0).unwrap();
        encode_branch(iced_x86::Code::Je_rel32_64, 0, n).unwrap();

        encode_branch(iced_x86::Code::Jmp_rel32_64, n, 0).unwrap();
        encode_branch(iced_x86::Code::Jmp_rel32_64, 0, n).unwrap();
    }
}
