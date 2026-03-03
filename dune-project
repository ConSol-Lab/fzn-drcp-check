(lang dune 3.18)

(using coq 0.10)

(using menhir 3.0)

(package
 (name drcpcheck)
 (synopsis "Flatzinc-DRCP Checker")
 (description "Formally verified DRCP proof checker for FlatZinc models")
 (depends
  angstrom
  bigstringaf
  camlzip
  core_bench
  core_unix
  menhir
  ocaml-protoc
  pbrt
  zarith
  (coq
   (and
    (>= 8.20)
    (< 8.21)))
  coq-menhirlib
  coq-mmaps
  ppx_import
  ppx_inline_test))

(source
 (github ConSol-Lab/fzn-drcp-check))

(authors "Maarten Flippo" "Konstantin Sidorov")

(license MIT)
