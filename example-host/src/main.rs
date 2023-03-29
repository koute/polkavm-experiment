use core::ops::ControlFlow;
use polkavm::{
    isa::Reg,
    jit::{CompileConfig, InstanceRef, Module, Program, UserContext},
};

struct User {}

impl UserContext for User {
    fn on_ecall(&mut self, instance: &mut InstanceRef) -> ControlFlow<()> {
        match instance.get_reg(Reg::A0) {
            259 => {
                let ptr = instance.get_reg(Reg::A1);
                let length = instance.get_reg(Reg::A2);
                let slice = &instance.memory()[ptr as usize..(ptr + length) as usize];
                if let Ok(s) = std::str::from_utf8(&slice) {
                    println!("{}", s);
                } else {
                    println!("ERR: invalid UTF-8 passed to the println host call");
                }

                ControlFlow::Continue(())
            }
            260 => ControlFlow::Break(()),
            reg => {
                println!("ERR: unknown ecall: {}", reg);
                ControlFlow::Break(())
            }
        }
    }
}

fn main() {
    env_logger::init();

    let raw_program = include_bytes!("../../target/riscv32i-unknown-none-elf/minimal/example-payload");
    let program = Program::new(raw_program);
    let mut config = CompileConfig::default();
    config.set_memory_size(2 * 1024 * 1024);
    let module = Module::compile(&program, config);
    let user = User {};

    let mut instance = module.instantiate(user);
    instance.run();
}
