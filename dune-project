(lang dune 3.0)
(using menhir 2.1)

(name sys4lang)
(version 0.2.0)

(generate_opam_files true)

(source
 (github kichikuou/sys4lang))

(authors "kichikuou <KichikuouChrome@gmail.com>")

(maintainers "kichikuou <KichikuouChrome@gmail.com>")

(license GPL-2.0-or-later)

(documentation https://github.com/kichikuou/sys4lang)

(package
  (name sys4lang)
  (synopsis "Compiler and language server for the System 4 programming language")
  (description "\| A compiler and language server for AliceSoft's System 4
               "\| programming language.
               )
  (depends
   ocaml
   base
   cmdliner
   stdio
   camlzip
   vector
   dune
   dune-build-info
   (linol-lwt (and (>= "0.8") (< "0.10")))
   menhir
   yojson
   ppx_yojson_conv_lib
   (ppx_expect :with-test)
   (ocamlformat (= 0.27.0))))
