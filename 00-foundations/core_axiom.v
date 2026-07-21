(* THE ONLY AXIOM *)
Inductive Sym3 : Type :=
  | I : Sym3    (* Identity  — 0° axis  — OR  = 0 *)
  | N : Sym3    (* Inverse   — 90° axis — AND = 1 *)
  | F : Sym3.   (* Fixed/Far — 45° axis — DIV = / *)

(* 0 and 1 are BOTH symbols AND operators *)
Inductive Op3 : Type :=
  | OpOR  : Op3   (* 0 = OR  = additive   *)
  | OpAND : Op3   (* 1 = AND = multiplicative *)
  | OpDIV : Op3.  (* / = ratio = diagonal *)

(* Operators ARE their axis symbols — proved, not assumed *)
Theorem op_sym_correspondence :
  op_axis OpOR  = sym_axis I /\   (* 0 = OR  lives on 0°  *)
  op_axis OpAND = sym_axis N /\   (* 1 = AND lives on 90° *)
  op_axis OpDIV = sym_axis F.     (* / = DIV lives on 45° *)
Proof. repeat split; reflexivity. Qed.
