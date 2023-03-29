#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Reg {
    Zero = 0,
    RA,
    SP,
    GP,
    TP,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum BranchKind {
    Eq = 0b000,
    NotEq = 0b001,
    LessSigned = 0b100,
    GreaterOrEqualSigned = 0b101,
    LessUnsigned = 0b110,
    GreaterOrEqualUnsigned = 0b111,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum LoadKind {
    I8 = 0b000,
    I16 = 0b001,
    U32 = 0b010,
    U8 = 0b100,
    U16 = 0b101,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum StoreKind {
    U8 = 0b000,
    U16 = 0b001,
    U32 = 0b010,
}

impl StoreKind {
    #[inline(always)]
    const fn decode(value: u32) -> Option<Self> {
        match value & 0b111 {
            0b000 => Some(StoreKind::U8),
            0b001 => Some(StoreKind::U16),
            0b010 => Some(StoreKind::U32),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum RegImmKind {
    Add = 0b000,                 // ADDI
    SetLessThanSigned = 0b010,   // SLTI
    SetLessThanUnsigned = 0b011, // SLTIU
    Xor = 0b100,                 // XORI
    Or = 0b110,                  // ORI
    And = 0b111,                 // ANDI
}

impl RegImmKind {
    #[inline(always)]
    const fn decode(value: u32) -> Option<Self> {
        match value & 0b111 {
            0b000 => Some(Self::Add),
            0b010 => Some(Self::SetLessThanSigned),
            0b011 => Some(Self::SetLessThanUnsigned),
            0b100 => Some(Self::Xor),
            0b110 => Some(Self::Or),
            0b111 => Some(Self::And),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum ShiftKind {
    LogicalLeft,
    LogicalRight,
    ArithmeticRight,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum RegRegKind {
    Add,
    Sub,
    ShiftLogicalLeft,
    SetLessThanSigned,
    SetLessThanUnsigned,
    Xor,
    ShiftLogicalRight,
    ShiftArithmeticRight,
    Or,
    And,
    Mul,
    MulUpperSignedSigned,
    MulUpperUnsignedUnsigned,
    MulUpperSignedUnsigned,
    Div,
    DivUnsigned,
    Rem,
    RemUnsigned,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u32)]
pub enum Inst {
    LoadUpperImmediate {
        dst: Reg,
        value: u32,
    },
    AddUpperImmediateToPc {
        dst: Reg,
        value: u32,
    },
    JumpAndLink {
        dst: Reg,
        target: u32,
    },
    JumpAndLinkRegister {
        dst: Reg,
        base: Reg,
        value: i32,
    },
    Branch {
        kind: BranchKind,
        src1: Reg,
        src2: Reg,
        target: u32,
    },
    Load {
        kind: LoadKind,
        dst: Reg,
        base: Reg,
        offset: i32,
    },
    Store {
        kind: StoreKind,
        src: Reg,
        base: Reg,
        offset: i32,
    },
    RegImm {
        kind: RegImmKind,
        dst: Reg,
        src: Reg,
        imm: i32,
    },
    Shift {
        kind: ShiftKind,
        dst: Reg,
        src: Reg,
        amount: u8,
    },
    RegReg {
        kind: RegRegKind,
        dst: Reg,
        src1: Reg,
        src2: Reg,
    },
    Ecall,
    Unimplemented,
}

impl Reg {
    #[inline(always)]
    pub const fn decode(reg: u32) -> Self {
        match reg & 0b11111 {
            0 => Self::Zero,
            1 => Self::RA,
            2 => Self::SP,
            3 => Self::GP,
            4 => Self::TP,
            5 => Self::T0,
            6 => Self::T1,
            7 => Self::T2,
            8 => Self::S0,
            9 => Self::S1,
            10 => Self::A0,
            11 => Self::A1,
            12 => Self::A2,
            13 => Self::A3,
            14 => Self::A4,
            15 => Self::A5,
            16 => Self::A6,
            17 => Self::A7,
            18 => Self::S2,
            19 => Self::S3,
            20 => Self::S4,
            21 => Self::S5,
            22 => Self::S6,
            23 => Self::S7,
            24 => Self::S8,
            25 => Self::S9,
            26 => Self::S10,
            27 => Self::S11,
            28 => Self::T3,
            29 => Self::T4,
            30 => Self::T5,
            31 => Self::T6,
            _ => unreachable!(),
        }
    }
}

#[inline(always)]
const fn sign_ext(value: u32, bits: u32) -> i32 {
    let mask = 1 << (bits - 1);
    (value ^ mask) as i32 - mask as i32
}

#[test]
fn test_sign_ext() {
    assert_eq!(sign_ext(0b101, 4), 0b101);

    assert_eq!(sign_ext(0b101, 3) as u32, 0b11111111111111111111111111111101);

    assert_eq!(sign_ext(0b001, 3) as u32, 0b001);
}

#[inline(always)]
const fn bits(start: u32, end: u32, value: u32, position: u32) -> u32 {
    let mask = (1 << (end - start + 1)) - 1;
    ((value >> position) & mask) << start
}

impl Inst {
    pub fn decode(op: u32, pc: u32) -> Option<Self> {
        debug_assert_eq!(pc % 4, 0);

        // This is mostly unofficial, but it's a defacto standard used by both LLVM and GCC.
        // https://github.com/riscv-non-isa/riscv-asm-manual/blob/master/riscv-asm.md#instruction-aliases
        if op == 0xc0001073 {
            return Some(Inst::Unimplemented);
        }

        match op & 0b1111111 {
            0b0110111 => {
                // LUI
                Some(Inst::LoadUpperImmediate {
                    dst: Reg::decode(op >> 7),
                    value: op & 0xfffff000,
                })
            }
            0b0010111 => {
                // AUIPC
                Some(Inst::AddUpperImmediateToPc {
                    dst: Reg::decode(op >> 7),
                    value: op & 0xfffff000,
                })
            }
            0b1101111 => {
                // JAL
                Some(Inst::JumpAndLink {
                    dst: Reg::decode(op >> 7),
                    target: (sign_ext(
                        bits(1, 10, op, 21) | bits(11, 11, op, 20) | bits(12, 19, op, 12) | bits(20, 20, op, 31),
                        21,
                    ) + pc as i32) as u32,
                })
            }
            0b1100111 => {
                // JALR
                match (op >> 12) & 0b111 {
                    0b000 => Some(Inst::JumpAndLinkRegister {
                        dst: Reg::decode(op >> 7),
                        base: Reg::decode(op >> 15),
                        value: sign_ext(op >> 20, 12),
                    }),
                    _ => None,
                }
            }
            0b1100011 => {
                let kind = match (op >> 12) & 0b111 {
                    0b000 => BranchKind::Eq,
                    0b001 => BranchKind::NotEq,
                    0b100 => BranchKind::LessSigned,
                    0b101 => BranchKind::GreaterOrEqualSigned,
                    0b110 => BranchKind::LessUnsigned,
                    0b111 => BranchKind::GreaterOrEqualUnsigned,
                    _ => return None,
                };

                Some(Inst::Branch {
                    kind,
                    src1: Reg::decode(op >> 15),
                    src2: Reg::decode(op >> 20),
                    target: (sign_ext(
                        bits(1, 4, op, 8) | bits(5, 10, op, 25) | bits(11, 11, op, 7) | bits(12, 12, op, 31),
                        13,
                    ) + pc as i32) as u32,
                })
            }
            0b0000011 => {
                let kind = match (op >> 12) & 0b111 {
                    0b000 => LoadKind::I8,
                    0b001 => LoadKind::I16,
                    0b010 => LoadKind::U32,
                    0b100 => LoadKind::U8,
                    0b101 => LoadKind::U16,
                    _ => return None,
                };

                Some(Inst::Load {
                    kind,
                    dst: Reg::decode(op >> 7),
                    base: Reg::decode(op >> 15),
                    offset: sign_ext((op >> 20) & 0b111111111111, 12),
                })
            }
            0b0100011 => Some(Inst::Store {
                kind: StoreKind::decode(op >> 12)?,
                base: Reg::decode(op >> 15),
                src: Reg::decode(op >> 20),
                offset: sign_ext(((op >> (25 - 5)) & 0b111111100000) | ((op >> 7) & 0b11111), 12),
            }),
            0b0010011 => match (op >> 12) & 0b111 {
                0b001 => {
                    if op & 0xfe000000 != 0 {
                        return None;
                    }

                    Some(Inst::Shift {
                        kind: ShiftKind::LogicalLeft,
                        dst: Reg::decode(op >> 7),
                        src: Reg::decode(op >> 15),
                        amount: bits(0, 4, op, 20) as u8,
                    })
                }
                0b101 => {
                    let kind = match (op & 0xfe000000) >> 24 {
                        0b00000000 => ShiftKind::LogicalRight,
                        0b01000000 => ShiftKind::ArithmeticRight,
                        _ => return None,
                    };

                    Some(Inst::Shift {
                        kind,
                        dst: Reg::decode(op >> 7),
                        src: Reg::decode(op >> 15),
                        amount: bits(0, 4, op, 20) as u8,
                    })
                }
                _ => Some(Inst::RegImm {
                    kind: RegImmKind::decode(op >> 12)?,
                    dst: Reg::decode(op >> 7),
                    src: Reg::decode(op >> 15),
                    imm: sign_ext(op >> 20, 12),
                }),
            },
            0b0110011 => {
                let kind = match op & 0b1111111_00000_00000_111_00000_0000000 {
                    0b0000000_00000_00000_000_00000_0000000 => RegRegKind::Add,
                    0b0100000_00000_00000_000_00000_0000000 => RegRegKind::Sub,
                    0b0000000_00000_00000_001_00000_0000000 => RegRegKind::ShiftLogicalLeft,
                    0b0000000_00000_00000_010_00000_0000000 => RegRegKind::SetLessThanSigned,
                    0b0000000_00000_00000_011_00000_0000000 => RegRegKind::SetLessThanUnsigned,
                    0b0000000_00000_00000_100_00000_0000000 => RegRegKind::Xor,
                    0b0000000_00000_00000_101_00000_0000000 => RegRegKind::ShiftLogicalRight,
                    0b0100000_00000_00000_101_00000_0000000 => RegRegKind::ShiftArithmeticRight,
                    0b0000000_00000_00000_110_00000_0000000 => RegRegKind::Or,
                    0b0000000_00000_00000_111_00000_0000000 => RegRegKind::And,

                    0b0000001_00000_00000_000_00000_0000000 => RegRegKind::Mul,
                    0b0000001_00000_00000_001_00000_0000000 => RegRegKind::MulUpperSignedSigned,
                    0b0000001_00000_00000_010_00000_0000000 => RegRegKind::MulUpperUnsignedUnsigned,
                    0b0000001_00000_00000_011_00000_0000000 => RegRegKind::MulUpperSignedUnsigned,
                    0b0000001_00000_00000_100_00000_0000000 => RegRegKind::Div,
                    0b0000001_00000_00000_101_00000_0000000 => RegRegKind::DivUnsigned,
                    0b0000001_00000_00000_110_00000_0000000 => RegRegKind::Rem,
                    0b0000001_00000_00000_111_00000_0000000 => RegRegKind::RemUnsigned,
                    _ => return None,
                };

                Some(Inst::RegReg {
                    kind,
                    dst: Reg::decode(op >> 7),
                    src1: Reg::decode(op >> 15),
                    src2: Reg::decode(op >> 20),
                })
            }
            0b1110011 => {
                if op == 0b000000000000_00000_000_00000_1110011 {
                    Some(Inst::Ecall)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[test]
fn test_decode_jump_and_link() {
    assert_eq!(
        Inst::decode(0xd6dff06f, 0xa1d4).unwrap(),
        Inst::JumpAndLink {
            dst: Reg::Zero,
            target: 0x9f40
        }
    );
}

#[test]
fn test_decode_branch() {
    assert_eq!(
        Inst::decode(0x00c5fe63, 0x70).unwrap(),
        Inst::Branch {
            kind: BranchKind::GreaterOrEqualUnsigned,
            src1: Reg::A1,
            src2: Reg::A2,
            target: 0x8c
        }
    );

    assert_eq!(
        Inst::decode(0xfeb96ce3, 0xccc4).unwrap(),
        Inst::Branch {
            kind: BranchKind::LessUnsigned,
            src1: Reg::S2,
            src2: Reg::A1,
            target: 0xccbc
        }
    );
}
