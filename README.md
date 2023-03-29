WARNING: All of this code is highly experimental and is a direct result of a two day hacking binge fueled by a truckload of tea.
It's definitely not safe to use, and if you value your sanity it might not even be safe to read. Enter at your own peril!

This crate contains a simple singlepass RISC-V to AMD64 recompiler.

## Example

1. Install the necessary target: `rustup target add riscv32i-unknown-none-elf`
2. Compile the payload with `build-example-payload.sh`
3. Run `cargo run -p example-host` to run it in a VM.

## License

Licensed under either of

  * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
  * MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
