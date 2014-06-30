Require Import Interpreter.

Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> failwith ""FIXME: No extraction from binary float allowed yet."")"
].


(* That would be more optimized than char lists...
Extract Inductive String.string => "string" [ """""" "(^)" ]. *)

Extraction Blacklist String List Bool.

Separate Extraction Interpreter Values Syntax.
