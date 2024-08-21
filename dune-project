(lang dune 3.16)
(using coq 0.8)

(name fzn_drcp_check)

(generate_opam_files true)

(source
 (github ConSol-Lab/fzn-drcp-check))

(authors "Maarten Flippo" "Konstantin Sidorov")

(maintainers "Maarten Flippo" "Konstantin Sidorov")

(license MIT)

(package
 (name fzn_drcp_check)
 (depends ocaml dune))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
