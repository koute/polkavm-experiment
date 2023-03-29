#![no_std]
#![no_main]

extern crate alloc;

#[repr(C)]
struct Heap {
    memory: [u8; 1024 * 1024],
    bump: usize,
}

#[inline(always)]
unsafe fn get_heap() -> &'static mut Heap {
    static mut HEAP: Heap = Heap {
        memory: [0; 1024 * 1024],
        bump: 0,
    };

    &mut HEAP
}

#[inline(always)]
unsafe fn initialize_heap() {
    let heap = get_heap();
    heap.bump = core::mem::size_of::<dlmalloc::Dlmalloc<Allocator>>();

    core::ptr::write(
        heap.memory.as_mut_ptr().cast(),
        dlmalloc::Dlmalloc::new_with_allocator(Allocator),
    );
}

struct Allocator;

unsafe impl dlmalloc::Allocator for Allocator {
    fn alloc(&self, size: usize) -> (*mut u8, usize, u32) {
        unsafe {
            let heap = get_heap();
            if size > heap.memory.len() - heap.bump {
                println("FATAL ERROR: ALLOCATION FAILED");
                return (core::ptr::null_mut(), 0, 0);
            }

            let ptr = heap.memory.as_mut_ptr().add(heap.bump);
            heap.bump += size;
            (ptr, size, 0)
        }
    }
    fn remap(&self, _ptr: *mut u8, _oldsize: usize, _newsize: usize, _can_move: bool) -> *mut u8 {
        core::ptr::null_mut()
    }
    fn free_part(&self, _ptr: *mut u8, _oldsize: usize, _newsize: usize) -> bool {
        false
    }
    fn free(&self, _ptr: *mut u8, _size: usize) -> bool {
        false
    }
    fn can_release_part(&self, _flags: u32) -> bool {
        false
    }
    fn allocates_zeros(&self) -> bool {
        true
    }
    fn page_size(&self) -> usize {
        4096
    }
}

#[global_allocator]
static mut ALLOC: Allocator = Allocator;

unsafe impl alloc::alloc::GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: alloc::alloc::Layout) -> *mut u8 {
        <Allocator as dlmalloc::Allocator>::alloc(&Allocator, layout.size()).0
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: alloc::alloc::Layout) {
        <Allocator as dlmalloc::Allocator>::free(&Allocator, ptr, layout.size());
    }
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    println("Panic!");
    println(&alloc::format!("{}", info));
    loop {}
}

fn println(slice: &str) {
    #[cfg(target_arch = "riscv32")]
    unsafe {
        core::arch::asm!(
            "li a0, 259",
            "ecall",
            in("a1") slice.as_ptr(),
            in("a2") slice.len(),
            lateout("a0") _
        );
    }
}

fn exit() -> ! {
    #[cfg(target_arch = "riscv32")]
    unsafe {
        core::arch::asm!(
            "li a0, 260",
            "ecall",
            lateout("a0") _
        );

        core::hint::unreachable_unchecked();
    }
}

#[cfg_attr(target_arch = "riscv32", link_section = ".init")]
#[no_mangle]
pub extern "C" fn main() {
    unsafe {
        initialize_heap();
    }

    println("Hello, world!");
    println(&alloc::format!("{} + {} = {}", 1.23, 3.45, 1.23 + 3.45));
    exit();
}
