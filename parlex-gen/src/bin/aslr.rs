#[cfg(feature = "cli")]
mod real {
    use clap::Parser;
    use parlex_gen::aslr;
    use std::path::PathBuf;

    #[derive(Parser)]
    #[command(about = "Generate parser code from ASLR grammar")]
    struct Args {
        /// Path to the input ASLR grammar file
        #[arg(short = 'g', long)]
        grammar: PathBuf,

        /// Path to write the generated Rust source code
        #[arg(short = 'R', long)]
        rust: PathBuf,
    }

    pub fn main() -> anyhow::Result<()> {
        let args = Args::parse();
        aslr::generate(args.grammar, args.rust)
    }
}

#[cfg(feature = "cli")]
fn main() -> anyhow::Result<()> {
    real::main()
}

#[cfg(not(feature = "cli"))]
fn main() {
    eprintln!("pargen disabled (compiled without `cli` feature)");
}
