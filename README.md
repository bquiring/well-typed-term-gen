
A well-typed program generator framework written in OCaml.

This repo is under heavy development to create a cohesive interface for writing generators for new languages.

Dependencies:
* OCaml
* Dune

Opam Dependencies:
* `unionFind`
```
opam install unionFind
```

to build:
```
dune build
```


To generate many terms that are dumped to the command line:
```
dune exec -- gen_sml -n 10 -size 15
```

To generate many terms that are passed to Standard ML:
```
dune exec -- gen_sml -n 10 -size 15 > test.sml
sml test.sml
```
