# FZN DRCP Checker

A formally verified checker for the FlatZinc (FZN) constraint-model format and
the DRCP (Deletion Reverse-unit-propagation Constraint Proof) proof format.

## Dependencies

The project requires Rocq/Coq 8.20. The following OPAM packages should be installed:
- `menhir`
- `coq-menhirlib`
- `angstrom`
- `ppx_import`
- `ppx_inline_test`
- `coq-mmaps`, for which you need to add a repository: 
  ```
  opam repo add coq-released https://coq.inria.fr/opam/released
  ```

## Building

To build the compiler, use the [dune](https://dune.build/) build tool. Building 
is done by running
```
dune build
```
in the root directory. Alternatively, the checker can be executed directly by
`dune` by running
```
dune exec fzn_drcp_check -- <args>
```

## Proof formats and options

Pass either a text (`.drcp`) or binary (`.bin`) DRCP proof — the format is inferred from the file extension (override with `--drcp-format text|binary`).  Both input formats may further be gzipped (`.drcp.gz` / `.bin.gz`).

Pass `-s` to check the proof incrementally (step by step, without loading it all at once).  Use `--bufsz N` to set the read-buffer size (in bytes, default 1 MiB).

```
dune exec fzn_drcp_check -- <model.fzn> <proof.bin>    # binary proof
dune exec fzn_drcp_check -- -s <model.fzn> <proof.drcp>   # streamed
```

## Documentation

Run
```
dune build @doc
```

After which you can browse the coqdoc documentation in `_build/default/theories/Checker.html`.

We use https://github.com/rocq-community/coqdocjs under the BSD-2 Clause license to make everything look nicer. See https://github.com/rocq-community/coqdocjs/issues/17 for it is configured with dune.
