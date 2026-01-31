(lang dune 3.13)
(using menhir 3.0)

(name sys4lang)
(version 0.7.2)

(generate_opam_files true)

(source
 (github kichikuou/sys4lang))

(authors "kichikuou <KichikuouChrome@gmail.com>")

(maintainers "kichikuou <KichikuouChrome@gmail.com>")

(license GPL-2.0-or-later)

(documentation https://github.com/kichikuou/sys4lang)

(package
  (name sys4lang)
  (synopsis "System 4 language tool suite")
  (description "\| Compiler, decompiler and language server for AliceSoft's
               "\| System 4 programming language.
               )
  (depends
   (ocaml (>= "5.2"))
   base
   cmdliner
   stdio
   camlzip
   dune
   dune-build-info
   (linol-eio (and (>= "0.8") (< "0.10")))
   eio_main
   fpath
   menhir
   yojson
   ppx_deriving
   (ppx_yojson_conv :with-test)
   ppx_yojson_conv_lib
   (ppx_expect :with-test)
   (ocamlformat (and (= 0.28.1) :with-test))))
