#[cfg(feature = "cli")]
mod real {
    use clap::Parser;
    use parlex_gen::alex;
    use std::path::PathBuf;

    #[derive(Parser)]
    #[command(about = "Generate lexer code from ALEX spec")]
    struct Args {
        /// Path to the input Alex specification file
        #[arg(short = 's', long)]
        spec: PathBuf,

        /// Path to write the generated Rust source code
        #[arg(short = 'R', long)]
        rust: PathBuf,

        /// Path to write the generated DFA in binary big-endian format
        #[arg(short = 'B', long)]
        dfa_be: PathBuf,

        /// Path to write the generated DFA in binary little-endian format
        #[arg(short = 'L', long)]
        dfa_le: PathBuf,
    }

    pub fn main() -> anyhow::Result<()> {
        let args = Args::parse();
        alex::generate(args.spec, args.rust, args.dfa_be, args.dfa_le)
    }
}

#[cfg(feature = "cli")]
fn main() -> anyhow::Result<()> {
    real::main()
}

#[cfg(not(feature = "cli"))]
fn main() {
    eprintln!("lexgen disabled (compiled without `cli` feature)");
}
