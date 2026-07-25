(* ================================================================= *)
(*  HopfPoly.v                                                        *)
(*                                                                    *)
(*  THE BINOMIAL HOPF ALGEBRA on ℤ[X]  (coordinate ring of 𝔾ₐ).      *)
(*                                                                    *)
(*  H = ℤ[X] carries a Hopf-algebra structure:                        *)
(*     coproduct   Δ(p) = p(X + Y)          (Δ : H → H⊗H)            *)
(*     counit      ε(p) = p(0)                                        *)
(*     antipode    S(p)(X) = p(−X)                                    *)
(*  X is a primitive element (Δ X = X⊗1 + 1⊗X), and the formal        *)
(*  derivative is the derivation it generates (Leibniz = product      *)
(*  rule).                                                             *)
(*                                                                    *)
(*  H⊗H is represented concretely as `list poly`: a tensor            *)
(*  t = Σ_i X^i ⊗ (row_i) with row_i ∈ ℤ[Y].  A faithful bivariate    *)
(*  evaluation `beval t x y = Σ_i x^i · row_i(y)` verifies every      *)
(*  Hopf axiom.  Polynomials are compared up to evaluation (the       *)
(*  representation-independent equality).  AXIOM-FREE.               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Require Import IntPoly PolyDiv IntPolyDeriv.
Open Scope Z_scope.

(* ================================================================= *)
(*  H ⊗ H  as list poly, and its bivariate evaluation                 *)
(* ================================================================= *)
Definition tensor := list poly.

(* beval t x y = Σ_i x^i · (row_i evaluated at y) *)
Definition beval (t : tensor) (x y : Z) : Z :=
  eval (map (fun row => eval row y) t) x.

Definition bconst (c : Z) : tensor := [[c]].
Definition bshiftX (t : tensor) : tensor := [] :: t.       (* multiply by X⊗1 *)
Definition bshiftY (t : tensor) : tensor := map (fun row => 0%Z :: row) t. (* by 1⊗X *)

Fixpoint badd (s t : tensor) : tensor :=
  match s, t with
  | [], _ => t
  | _, [] => s
  | a :: s', b :: t' => padd a b :: badd s' t'
  end.

Lemma map_evalrow_badd : forall s t y,
  map (fun row => eval row y) (badd s t)
  = padd (map (fun row => eval row y) s) (map (fun row => eval row y) t).
Proof.
  induction s as [|a s' IH]; intros [|b t'] y; simpl; try reflexivity.
  rewrite eval_add, IH; reflexivity.
Qed.

Lemma beval_badd : forall s t x y, beval (badd s t) x y = beval s x y + beval t x y.
Proof.
  intros; unfold beval; rewrite map_evalrow_badd, eval_add; reflexivity.
Qed.

Lemma beval_bconst : forall c x y, beval (bconst c) x y = c.
Proof. intros; unfold beval, bconst; simpl; ring. Qed.

Lemma beval_bshiftX : forall t x y, beval (bshiftX t) x y = x * beval t x y.
Proof. intros t x y; unfold beval, bshiftX; simpl; ring. Qed.

Lemma beval_bshiftY : forall t x y, beval (bshiftY t) x y = y * beval t x y.
Proof.
  intros t x y; unfold beval, bshiftY.
  induction t as [|row t' IH]; [ simpl; ring | ].
  simpl; rewrite IH; ring.
Qed.

(* ================================================================= *)
(*  The coproduct  Δ(p) = p(X + Y)                                    *)
(* ================================================================= *)
Fixpoint Delta (p : poly) : tensor :=
  match p with
  | [] => []
  | c :: p' => badd (bconst c) (badd (bshiftX (Delta p')) (bshiftY (Delta p')))
  end.

(* THE MASTER LEMMA: the coproduct evaluates to p(x+y). *)
Theorem beval_Delta : forall p x y, beval (Delta p) x y = eval p (x + y).
Proof.
  induction p as [|c p' IH]; intros x y.
  - unfold beval; simpl; ring.
  - cbn [Delta].
    rewrite beval_badd, beval_bconst, beval_badd, beval_bshiftX, beval_bshiftY, !IH.
    simpl; ring.
Qed.

(* ================================================================= *)
(*  Bialgebra: Δ is an algebra morphism                              *)
(*      Δ(p·q) = Δ(p)·Δ(q)      and     Δ(1) = 1⊗1                    *)
(*  (checked on the faithful bivariate evaluation)                    *)
(* ================================================================= *)
Theorem Delta_mult : forall p q x y,
  beval (Delta (pmul p q)) x y = beval (Delta p) x y * beval (Delta q) x y.
Proof. intros; rewrite !beval_Delta, eval_mul; reflexivity. Qed.

Theorem Delta_unit : forall x y, beval (Delta (pconst 1)) x y = 1.
Proof. intros; rewrite beval_Delta, eval_const; reflexivity. Qed.

(* ================================================================= *)
(*  Coassociativity:  (Δ⊗id)∘Δ = (id⊗Δ)∘Δ                            *)
(*  Coproducting either the left or the right factor and evaluating   *)
(*  agree — both give p(x+y+z).                                       *)
(* ================================================================= *)
Theorem coassoc : forall p x y z,
  beval (Delta p) (x + y) z = beval (Delta p) x (y + z).
Proof. intros; rewrite !beval_Delta; f_equal; ring. Qed.

(* ================================================================= *)
(*  Counit:  (ε⊗id)∘Δ = id  and  (id⊗ε)∘Δ = id                       *)
(*  ε picks the X^0-coefficient; ε on the second factor evaluates at 0*)
(* ================================================================= *)
Lemma eval_at_0 : forall L, eval L 0 = nth 0 L 0.
Proof. destruct L; simpl; ring. Qed.

Lemma nth0_map_eval : forall t y,
  nth 0 (map (fun row => eval row y) t) 0 = eval (nth 0 t []) y.
Proof. destruct t; simpl; reflexivity. Qed.

(* (ε⊗id)(t) = row_0 ;  (id⊗ε)(t) = Σ_i ε(row_i) X^i *)
Definition epsId (t : tensor) : poly := nth 0 t [].
Definition idEps (t : tensor) : poly := map (fun row => eval row 0) t.

Theorem counit_left : forall p y, eval (epsId (Delta p)) y = eval p y.
Proof.
  intros p y; unfold epsId.
  transitivity (beval (Delta p) 0 y).
  - unfold beval; rewrite eval_at_0; symmetry; apply nth0_map_eval.
  - rewrite beval_Delta; f_equal; ring.
Qed.

Theorem counit_right : forall p x, eval (idEps (Delta p)) x = eval p x.
Proof.
  intros p x; unfold idEps.
  change (eval (map (fun row => eval row 0) (Delta p)) x)
    with (beval (Delta p) x 0).
  rewrite beval_Delta; f_equal; ring.
Qed.

(* ================================================================= *)
(*  The antipode  S(p)(X) = p(−X)                                     *)
(* ================================================================= *)
Fixpoint Spoly (p : poly) : poly :=
  match p with [] => [] | c :: p' => c :: pneg (Spoly p') end.

Lemma eval_pneg : forall q x, eval (pneg q) x = - eval q x.
Proof. intros q x; change (pneg q) with (psub [] q); rewrite eval_sub; simpl; ring. Qed.

Theorem eval_S : forall p x, eval (Spoly p) x = eval p (- x).
Proof.
  induction p as [|c p' IH]; intro x; [ reflexivity | ].
  cbn [Spoly eval]; rewrite eval_pneg, IH; cbn [eval]; ring.
Qed.

(* ================================================================= *)
(*  The antipode axioms:  m∘(S⊗id)∘Δ = η∘ε = m∘(id⊗S)∘Δ              *)
(*  The convolutions S⋆id and id⋆S both collapse to p ↦ p(0)·1.       *)
(* ================================================================= *)
Lemma pow_negx : forall x i, (- x) ^ Z.of_nat i = (-1) ^ Z.of_nat i * x ^ Z.of_nat i.
Proof. intros; rewrite <- Z.pow_mul_l; f_equal; ring. Qed.

Lemma pow_negx_S : forall x i, (- x) ^ Z.of_nat (S i) = (- x) * (- x) ^ Z.of_nat i.
Proof. intros; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity. Qed.

Lemma pow_x_S : forall x i, x ^ Z.of_nat (S i) = x * x ^ Z.of_nat i.
Proof. intros; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity. Qed.

(* (S⋆id)(p) = Σ_i S(X^i)·row_i = Σ_i (−X)^i·row_i *)
Fixpoint conv_Sid (t : tensor) (i : nat) : poly :=
  match t with
  | [] => []
  | row :: t' => padd (pscale ((-1) ^ Z.of_nat i) (pmul (pmonom i) row)) (conv_Sid t' (S i))
  end.

Lemma eval_conv_Sid : forall t i x,
  eval (conv_Sid t i) x
  = (- x) ^ Z.of_nat i * eval (map (fun row => eval row x) t) (- x).
Proof.
  induction t as [|row t' IH]; intros i x; [ simpl; ring | ].
  cbn [conv_Sid map].
  rewrite eval_add, eval_scale, eval_mul, eval_monom, (IH (S i) x).
  cbn [eval]; rewrite pow_negx_S, Z.mul_assoc, <- pow_negx; ring.
Qed.

Theorem antipode_left : forall p x, eval (conv_Sid (Delta p) 0) x = eval p 0.
Proof.
  intros p x; rewrite eval_conv_Sid.
  change (Z.of_nat 0) with 0%Z; rewrite Z.pow_0_r, Z.mul_1_l.
  change (eval (map (fun row => eval row x) (Delta p)) (- x))
    with (beval (Delta p) (- x) x).
  rewrite beval_Delta; f_equal; ring.
Qed.

(* (id⋆S)(p) = Σ_i X^i·S(row_i) *)
Fixpoint conv_idS (t : tensor) (i : nat) : poly :=
  match t with
  | [] => []
  | row :: t' => padd (pmul (pmonom i) (Spoly row)) (conv_idS t' (S i))
  end.

Lemma eval_conv_idS : forall t i x,
  eval (conv_idS t i) x
  = x ^ Z.of_nat i * eval (map (fun row => eval row (- x)) t) x.
Proof.
  induction t as [|row t' IH]; intros i x; [ simpl; ring | ].
  cbn [conv_idS map].
  rewrite eval_add, eval_mul, eval_monom, eval_S, (IH (S i) x).
  cbn [eval]; rewrite pow_x_S; ring.
Qed.

Theorem antipode_right : forall p x, eval (conv_idS (Delta p) 0) x = eval p 0.
Proof.
  intros p x; rewrite eval_conv_idS.
  change (Z.of_nat 0) with 0%Z; rewrite Z.pow_0_r, Z.mul_1_l.
  change (eval (map (fun row => eval row (- x)) (Delta p)) x)
    with (beval (Delta p) x (- x)).
  rewrite beval_Delta; f_equal; ring.
Qed.

(* ================================================================= *)
(*  X is a PRIMITIVE element:  Δ(X) = X⊗1 + 1⊗X                       *)
(*  (X⊗1 + 1⊗X evaluates to x + y, matching Δ(X).)                    *)
(* ================================================================= *)
Theorem X_primitive : forall x y, beval (Delta (pmonom 1)) x y = x + y.
Proof.
  intros; rewrite beval_Delta, eval_monom.
  change (Z.of_nat 1) with 1%Z; rewrite Z.pow_1_r; reflexivity.
Qed.

(* ================================================================= *)
(*  DERIVATION BRIDGE: the formal derivative is the derivation        *)
(*  generated by the primitive X — Leibniz IS the coderivation law.   *)
(* ================================================================= *)
Theorem derivation_leibniz : forall p q x,
  eval (pderiv (pmul p q)) x = eval (pderiv p) x * eval q x + eval p x * eval (pderiv q) x.
Proof. exact pderiv_mul_eval. Qed.

Print Assumptions beval_Delta.
Print Assumptions antipode_left.
Print Assumptions X_primitive.

(* ================================================================= *)
(*  END HopfPoly.v                                                    *)
(*  ℤ[X] as the binomial Hopf algebra: coproduct Δ(p)=p(X+Y) is a     *)
(*  coassociative algebra morphism with counit p↦p(0) and antipode    *)
(*  p(X)↦p(−X); X is primitive and generates the formal derivative.   *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
