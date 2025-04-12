# Hack Assembler

[![unsafe forbidden]][safety dance] [![dependency badge]][deps.rs]

---

An assembler that translates programs written in the Hack assembly language into
Hack binary code. Based on the nand2tetris course, and written in Rust.

## Getting Started

You'll need to install Rust and its package manager, Cargo, on your system.
Please refer to the official [recommended Rust installation method] for your
system.

Note that you may need to use the nightly version of Rust. If you're using,
Rustup you can accomplish this like so:

```bash
rustup toolchain install nightly
```

You should also have some version of git installed. You can refer to the
[Git documentation] if you need help with that.

Clone the repository and navigate inside it:

```bash
git clone https://github.com/hashcatHitman/hack-assembler.git
cd hack-assembler
```

If you'd like to read the documentation, the reccommended way to do so is with:

```bash
cargo doc --document-private-items --open
```

Which will open the documentation in your browser.

To build the assembler binary, you can do:

```bash
cargo build --profile dev
```

Cargo will download the dependencies and compile the binary. It will be located
at `./target/debug/hack-assembler` or `./target/debug/hack-assembler.exe`,
depending on your system.

Though relative pathing seems to work fine, for the best experience it is
recommended to keep your `*.asm` files and the assembler in the same directory.
If you are doing so and are in the directory yourself, you can compile a `*.asm`
file to the equivalent `*.hack` file like so:

```bash
./hack-assembler foo.asm
```

Where `foo` can be variable, but should remain valid Unicode.

Please note that the assembler will refuse to compile `bar.asm` if `bar.hack` is
already present. You must delete or relocate existing files to recompile them.

[unsafe forbidden]: https://img.shields.io/badge/unsafe-forbidden-success.svg
[safety dance]: https://github.com/rust-secure-code/safety-dance/

[dependency badge]: https://deps.rs/repo/github/hashcatHitman/hack-assembler/status.svg
[deps.rs]: https://deps.rs/repo/github/hashcatHitman/hack-assembler

[recommended Rust installation method]: https://www.rust-lang.org/tools/install

[Git documentation]: https://git-scm.com/book/en/v2/Getting-Started-Installing-Git
