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

Definition sym_axis (s:Sym3) : nat := match s with I=>0 | N=>90 | F=>45 end.
Definition op_axis (o:Op3) : nat := match o with OpOR=>0 | OpAND=>90 | OpDIV=>45 end.

(* Operators ARE their axis symbols — proved, not assumed *)
Theorem op_sym_correspondence :
  op_axis OpOR  = sym_axis I /\   (* 0 = OR  lives on 0°  *)
  op_axis OpAND = sym_axis N /\   (* 1 = AND lives on 90° *)
  op_axis OpDIV = sym_axis F.     (* / = DIV lives on 45° *)
Proof. repeat split; reflexivity. Qed.
