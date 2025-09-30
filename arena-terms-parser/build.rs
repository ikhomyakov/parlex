// build.rs
use std::path::PathBuf;

fn main() {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    let input_file = PathBuf::from(&manifest_dir).join("src/term.alex");
    println!("cargo:rerun-if-changed={}", input_file.display());
    println!("cargo:warning=ALEX Input file is {}", input_file.display());
    println!(
        "cargo:warning=ALEX Output directory is {}",
        out_dir.display()
    );
    parlex_gen::alex::generate(&input_file, &out_dir, "lexer_data", false).unwrap();

    let input_file = PathBuf::from(&manifest_dir).join("src/termx.g");
    println!("cargo:rerun-if-changed={}", input_file.display());
    println!("cargo:warning=ASLR Input file is {}", input_file.display());
    println!(
        "cargo:warning=ASLR Output directory is {}",
        out_dir.display()
    );
    parlex_gen::aslr::generate(&input_file, &out_dir, "parser_data", false).unwrap();
}
