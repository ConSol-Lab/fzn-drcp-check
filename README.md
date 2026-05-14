# FZN DRCP Checker

A formally verified checker for the FZN model format and DRCP proof format.

## Dependencies

The following OPAM packages should be installed:
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

Currently to make it work you need to run it in release mode:
```
dune exec fzn_drcp_check --profile release
```

## Documentation

Run
```
dune build @doc
```

After which you can browse the coqdoc documentation in `_build/default/theories/Checker.html`.

We use https://github.com/rocq-community/coqdocjs under the BSD-2 Clause license to make everything look nicer. See https://github.com/rocq-community/coqdocjs/issues/17 for it is configured with dune.
