# FZN DRCP Checker

A formally verified checker for the FZN model format and DRCP proof format.

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
