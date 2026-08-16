//! The `lexlean` executable (SPEC.md §23).

#![forbid(unsafe_code)]

fn main() {
    std::process::exit(lexlean::cli::main_entry());
}
