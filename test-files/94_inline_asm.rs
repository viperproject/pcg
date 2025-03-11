fn main() {
    let x: u64;
    unsafe {
        std::arch::asm!(
            "mov {}, 42",
            out(reg) x
        );
    }
    // PCG: PcgError { kind: Unsupported(InlineAssembly), context: [] }
    println!("Value from assembly: {}", x);
}
