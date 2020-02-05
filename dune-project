(lang dune 2.0)
(name ScribbleCodeGen)

(generate_opam_files true)

(package
 (name ScribbleCodeGen)
 (depends
   base
   stdio
   menhir
   ocamlgraph)
)
(using menhir 2.0)
