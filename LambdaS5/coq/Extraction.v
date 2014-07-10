Set Implicit Arguments.
Require Import Interpreter.
Require Import JsNumber.


Require Import LibFix LibList.

Require Export Shared.
Require Export LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibNat LibEpsilon LibFunc LibHeap.
Require Flocq.Appli.Fappli_IEEE Flocq.Appli.Fappli_IEEE_bits.

Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

(*
(* We do not want “raise Not_found” to be at the toplevel. *)
Extraction Inline LibLogic.arbitrary.

Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> failwith ""FIXME: No extraction from binary float allowed yet."")"
].
*)





(*** Magical stuff from JSCert that makes float extraction work. *)


(* Optimal fixpoint. *)
Extraction Inline FixFun3 FixFun3Mod FixFun4 FixFun4Mod FixFunMod curry3 uncurry3 curry4 uncurry4.
(* As classical logic statements are now unused, they should not be extracted
   (otherwise, useless errors will be launched). *)
Extraction Inline epsilon epsilon_def classicT arbitrary indefinite_description Inhab_witness Fix isTrue.

(**************************************************************)
(** ** Numerical values *)

(* number *)

Extract Inductive positive => float
[ "(fun p -> 1. +. (2. *. p))"
  "(fun p -> 2. *. p)"
  "1." ]
"(fun f2p1 f2p f1 p ->
if p <= 1. then f1 () else if mod_float p 2. = 0. then f2p (p /. 2.) else f2p1 (p /. 2.))".

Extract Inductive Z => float [ "0." "" "(~-.)" ]
"(fun f0 fp fn z -> if z=0. then f0 () else if z>0. then fp z else fn (~-. z))".

Extract Inductive N => float [ "0." "" ]
"(fun f0 fp n -> if n=0. then f0 () else fp n)".

Extract Constant Z.add => "(+.)".
Extract Constant Z.succ => "(+.) 1.".
Extract Constant Z.pred => "(fun x -> x -. 1.)".
Extract Constant Z.sub => "(-.)".
Extract Constant Z.mul => "( *. )".
Extract Constant Z.opp => "(~-.)".
Extract Constant Z.abs => "abs_float".
Extract Constant Z.min => "min".
Extract Constant Z.max => "max".
Extract Constant Z.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".

Extract Constant Pos.add => "(+.)".
Extract Constant Pos.succ => "(+.) 1.".
Extract Constant Pos.pred => "(fun x -> x -. 1.)".
Extract Constant Pos.sub => "(-.)".
Extract Constant Pos.mul => "( *. )".
Extract Constant Pos.min => "min".
Extract Constant Pos.max => "max".
Extract Constant Pos.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".
Extract Constant Pos.compare_cont =>
 "fun x y c -> if x=y then c else if x<y then Lt else Gt".

Extract Constant N.add => "(+.)".
Extract Constant N.succ => "(+.) 1.".
Extract Constant N.pred => "(fun x -> x -. 1.)".
Extract Constant N.sub => "(-.)".
Extract Constant N.mul => "( *. )".
Extract Constant N.min => "min".
Extract Constant N.max => "max".
Extract Constant N.div => "(fun x y -> if x = 0. then 0. else floor (x /. y))".
Extract Constant N.modulo => "mod_float".
Extract Constant N.compare =>
 "fun x y -> if x=y then Eq else if x<y then Lt else Gt".


Extract Inductive Fappli_IEEE.binary_float => float [
  "(fun s -> if s then (0.) else (-0.))"
  "(fun s -> if s then infinity else neg_infinity)"
  "nan"
  "(fun (s, m, e) -> failwith ""FIXME: No extraction from binary float allowed yet."")"
].

Extract Constant JsNumber.of_int => "fun x -> x".

Extract Constant JsNumber.nan => "nan".
Extract Constant JsNumber.zero => "0.".
Extract Constant JsNumber.neg_zero => "(-0.)".
Extract Constant JsNumber.one => "1.".
Extract Constant JsNumber.infinity => "infinity".
Extract Constant JsNumber.neg_infinity => "neg_infinity".
Extract Constant JsNumber.max_value => "max_float".
Extract Constant JsNumber.min_value => "(Int64.float_of_bits Int64.one)".
Extract Constant JsNumber.floor => "floor".
Extract Constant JsNumber.absolute => "abs_float".
Extract Constant JsNumber.from_string =>
  "(fun s ->
    try
      let s = (String.concat """" (List.map (String.make 1) s)) in
      if s = """" then 0. else float_of_string s
    with Failure ""float_of_string"" -> nan)
   (* Note that we're using `float_of_string' there, which does not have the same
      behavior than JavaScript.  For instance it will read ""022"" as 22 instead of
      18, which should be the JavaScript result for it. *)".
Extract Constant JsNumber.to_string =>
  "(fun f -> 
    prerr_string (""Warning:  JsNumber.to_string called.  This might be responsible for errors.  Argument value:  "" ^ string_of_float f ^ ""."");
    prerr_newline();
    let string_of_number n =
      let inum = int_of_float n in
      if (float_of_int inum = n) then string_of_int inum else string_of_float n in
    let ret = ref [] in (* Ugly, but the API for OCaml string is not very functionnal... *)
    String.iter (fun c -> ret := c :: !ret) (string_of_number f);
    List.rev !ret)
   (* Note that this is ugly, we should use the spec of JsNumber.to_string here. *)".
Extract Constant JsNumber.add => "(+.)".
Extract Constant JsNumber.sub => "(-.)".
Extract Constant JsNumber.mult => "( *. )".
Extract Constant JsNumber.div => "(/.)".
Extract Constant JsNumber.fmod => "mod_float".
Extract Constant JsNumber.neg => "(~-.)".
Extract Constant JsNumber.sign => "(fun f -> float_of_int (compare f 0.))".
Extract Constant JsNumber.number_comparable => "(fun n1 n2 -> 0 = compare n1 n2)".
Extract Constant JsNumber.lt_bool => "(<)".

Extract Constant JsNumber.to_int32 => 
"fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let i31 = 2. ** 31. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    (if int32bit >= i31 then int32bit -. i32 else int32bit)
  | _ -> 0.". (* LATER:  do in Coq.  Spec is 9.5, p. 47.*)
Extract Constant JsNumber.to_uint32 =>
"fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    int32bit
  | _ -> 0.". (* LAER:  do in Coq.  Spec is 9.6, p47.*)
Extract Constant JsNumber.modulo_32 => "(fun x -> let r = mod_float x 32. in if x < 0. then r +. 32. else r)".
Extract Constant JsNumber.int32_bitwise_not => "fun x -> Int32.to_float (Int32.lognot (Int32.of_float x))".
Extract Constant JsNumber.int32_bitwise_and => "fun x y -> Int32.to_float (Int32.logand (Int32.of_float x) (Int32.of_float y))".
Extract Constant JsNumber.int32_bitwise_or => "fun x y -> Int32.to_float (Int32.logor (Int32.of_float x) (Int32.of_float y))".
Extract Constant JsNumber.int32_bitwise_xor => "fun x y -> Int32.to_float (Int32.logxor (Int32.of_float x) (Int32.of_float y))".
Extract Constant JsNumber.int32_left_shift => "(fun x y -> Int32.to_float (Int32.shift_left (Int32.of_float x) (int_of_float y)))".
Extract Constant JsNumber.int32_right_shift => "(fun x y -> Int32.to_float (Int32.shift_right (Int32.of_float x) (int_of_float y)))".
Extract Constant JsNumber.uint32_right_shift => 
"(fun x y ->
  let i31 = 2. ** 31. in
  let i32 = 2. ** 32. in
  let newx = if x >= i31 then x -. i32 else x in
  let r = Int32.to_float (Int32.shift_right_logical (Int32.of_float newx) (int_of_float y)) in
  if r < 0. then r +. i32 else r)".

Extract Constant int_of_char => "(fun c -> float_of_int (int_of_char c))".

Extract Constant ascii_compare => "(=)".
Extract Constant lt_int_decidable => "(<)".
Extract Constant le_int_decidable => "(<=)".
Extract Constant ge_nat_decidable => "(>=)".

(* TODO ARTHUR:  This TLC lemma does not extract to something computable... whereas it should! *)
Extract Constant prop_eq_decidable => "(=)".

(* The following functions make pattern matches with floats and shall thus be removed. *)
Extraction Inline Fappli_IEEE.Bplus Fappli_IEEE.binary_normalize Fappli_IEEE_bits.b64_plus.
Extraction Inline Fappli_IEEE.Bmult Fappli_IEEE.Bmult_FF Fappli_IEEE_bits.b64_mult.
Extraction Inline Fappli_IEEE.Bdiv Fappli_IEEE_bits.b64_div.

(* New options for the interpreter to work in Coq 8.4 *)
Set Extraction AccessOpaque.











Extract Constant Operators._print_string => "fun x -> print_string (CoqUtils.implode x); print_char '\n'".


(* That would be more optimized than char lists...
Extract Inductive String.string => "string" [ """""" "(^)" ]. *)

Extraction Blacklist String List Bool.

Separate Extraction Interpreter Values Syntax Store JsNumber.to_string.
