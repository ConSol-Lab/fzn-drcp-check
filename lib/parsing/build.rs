pub fn main() -> std::io::Result<()> {
    ocaml_build::Sigs::new("src/fzn_drcp_check_parsing.ml").generate()
}
