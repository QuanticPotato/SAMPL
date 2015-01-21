(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)

let local = false
let coqrunbyteflags = "-dllib -lcoqrun -dllpath '/usr/local/lib/coq'"
let coqlib = Some "/usr/local/lib/coq"
let configdir = None
let datadir = None
let docdir = "/usr/local/share/doc/coq"
let ocaml = "ocaml"
let ocamlc = "ocamlc"
let ocamlopt = "ocamlopt"
let ocamlmklib = "ocamlmklib"
let ocamldep = "ocamldep"
let ocamldoc = "ocamldoc"
let ocamlyacc = "ocamlyacc"
let ocamllex = "ocamllex"
let camlbin = "/usr/bin"
let camllib = "/usr/lib/ocaml"
let camlp4 = "camlp4"
let camlp4o = "camlp4orf"
let camlp4bin = "/usr/bin"
let camlp4lib = "+camlp4"
let camlp4compat = "-loc loc"
let coqideincl = ""
let cflags = "-Wall -Wno-unused"
let best = "opt"
let arch = "Linux"
let has_coqide = "no"
let gtk_platform = `X11
let has_natdynlink = true
let natdynlinkflag = "true"
let osdeplibs = "-cclib -lunix"
let version = "8.4pl4"
let caml_version = "4.01.0"
let date = "October 2014"
let compile_date = "Oct 09 2014 22:52:55"
let vo_magic_number = 08400
let state_magic_number = 58400
let exec_extension = ""
let with_geoproof = ref false
let browser = "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"
let wwwcoq = "http://coq.inria.fr/"
let wwwrefman = wwwcoq ^ "distrib/" ^ version ^ "/refman/"
let wwwstdlib = wwwcoq ^ "distrib/" ^ version ^ "/stdlib/"
let localwwwrefman = "file:/" ^ docdir ^ "html/refman"

let theories_dirs = [
"Arith";
"Bool";
"Classes";
"FSets";
"Init";
"Lists";
"Logic";
"MSets";
"NArith";
"Numbers";
"Numbers/Natural";
"Numbers/Natural/Binary";
"Numbers/Natural/BigN";
"Numbers/Natural/Peano";
"Numbers/Natural/Abstract";
"Numbers/Natural/SpecViaZ";
"Numbers/Cyclic";
"Numbers/Cyclic/ZModulo";
"Numbers/Cyclic/Abstract";
"Numbers/Cyclic/Int31";
"Numbers/Cyclic/DoubleCyclic";
"Numbers/Rational";
"Numbers/Rational/BigQ";
"Numbers/Rational/SpecViaQ";
"Numbers/NatInt";
"Numbers/Integer";
"Numbers/Integer/BigZ";
"Numbers/Integer/Binary";
"Numbers/Integer/Abstract";
"Numbers/Integer/SpecViaZ";
"Numbers/Integer/NatPairs";
"PArith";
"Program";
"QArith";
"Reals";
"Relations";
"Setoids";
"Sets";
"Sorting";
"Strings";
"Structures";
"Unicode";
"Vectors";
"Wellfounded";
"ZArith";
]
let plugins_dirs = [
"cc";
"decl_mode";
"extraction";
"field";
"firstorder";
"fourier";
"funind";
"micromega";
"nsatz";
"omega";
"quote";
"ring";
"romega";
"rtauto";
"setoid_ring";
"subtac";
"subtac/test";
"syntax";
"xml";
]
