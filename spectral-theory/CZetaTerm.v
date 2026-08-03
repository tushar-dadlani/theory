(* ================================================================= *)
(*  CZetaTerm.v  —  the complex Euler–Maclaurin term and its bound.    *)
(*                                                                    *)
(*  Part 1: derivatives of Re/Im of (c^w · K) for a complex constant   *)
(*  K (needed for the antiderivative G(x)=x^{1-s}/(1-s), whose         *)
(*  derivative is x^{-s}), and the modulus of the base derivative      *)
(*  |w·x^{w-1}| = |w|·x^{Re w-1}.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CPowBase.
Open Scope R_scope.

(* modulus of the base derivative  w·x^{w-1} *)
Lemma Cmod_wCpw : forall w x,
  Cmod (Cmul w (Cpw x (Cminus w C1))) = Cmod w * Rpower x (Re w - 1).
Proof.
  intros w x; rewrite Cmod_mul, Cpw_mod.
  replace (Re (Cminus w C1)) with (Re w - 1)
    by (unfold Cminus, Cadd, Copp, C1; simpl; ring).
  reflexivity.
Qed.

(* derivative of Re/Im of (c^w · K) in the base *)
Lemma Re_Cmul_deriv : forall w K x, 0 < x ->
  derivable_pt_lim (fun t => Re (Cmul (Cpw t w) K)) x
    (Re (Cmul (Cmul w (Cpw x (Cminus w C1))) K)).
Proof.
  intros w K x Hx.
  assert (Heq : (fun t => Re (Cmul (Cpw t w) K))
              = (fun t => Re K * Re (Cpw t w) - Im K * Im (Cpw t w)))
    by (apply functional_extensionality; intro t; unfold Cmul; cbn [Re]; ring).
  rewrite Heq.
  replace (Re (Cmul (Cmul w (Cpw x (Cminus w C1))) K))
    with (Re K * Re (Cmul w (Cpw x (Cminus w C1)))
          - Im K * Im (Cmul w (Cpw x (Cminus w C1))))
    by (unfold Cmul; cbn [Re Im]; ring).
  apply (derivable_pt_lim_minus
           (fun t => Re K * Re (Cpw t w)) (fun t => Im K * Im (Cpw t w)) x
           (Re K * Re (Cmul w (Cpw x (Cminus w C1))))
           (Im K * Im (Cmul w (Cpw x (Cminus w C1))))).
  - apply (derivable_pt_lim_scal (fun t => Re (Cpw t w)) (Re K) x
             (Re (Cmul w (Cpw x (Cminus w C1))))); apply Re_Cpw_deriv; exact Hx.
  - apply (derivable_pt_lim_scal (fun t => Im (Cpw t w)) (Im K) x
             (Im (Cmul w (Cpw x (Cminus w C1))))); apply Im_Cpw_deriv; exact Hx.
Qed.

Lemma Im_Cmul_deriv : forall w K x, 0 < x ->
  derivable_pt_lim (fun t => Im (Cmul (Cpw t w) K)) x
    (Im (Cmul (Cmul w (Cpw x (Cminus w C1))) K)).
Proof.
  intros w K x Hx.
  assert (Heq : (fun t => Im (Cmul (Cpw t w) K))
              = (fun t => Re K * Im (Cpw t w) + Im K * Re (Cpw t w)))
    by (apply functional_extensionality; intro t; unfold Cmul; cbn [Im]; ring).
  rewrite Heq.
  replace (Im (Cmul (Cmul w (Cpw x (Cminus w C1))) K))
    with (Re K * Im (Cmul w (Cpw x (Cminus w C1)))
          + Im K * Re (Cmul w (Cpw x (Cminus w C1))))
    by (unfold Cmul; cbn [Re Im]; ring).
  apply (derivable_pt_lim_plus
           (fun t => Re K * Im (Cpw t w)) (fun t => Im K * Re (Cpw t w)) x
           (Re K * Im (Cmul w (Cpw x (Cminus w C1))))
           (Im K * Re (Cmul w (Cpw x (Cminus w C1))))).
  - apply (derivable_pt_lim_scal (fun t => Im (Cpw t w)) (Re K) x
             (Im (Cmul w (Cpw x (Cminus w C1))))); apply Im_Cpw_deriv; exact Hx.
  - apply (derivable_pt_lim_scal (fun t => Re (Cpw t w)) (Im K) x
             (Re (Cmul w (Cpw x (Cminus w C1))))); apply Re_Cpw_deriv; exact Hx.
Qed.

(* ================================================================= *)
(*  Part 2: the complex EM term, its antiderivative relations, and     *)
(*  real-analysis helpers for the double-MVT bound.                    *)
(* ================================================================= *)

Definition gC (s : C) (x : R) : C := Cpw x (Copp s).
Definition GC (s : C) (x : R) : C := Cmul (Cpw x (Cminus C1 s)) (Cinv (Cminus C1 s)).
Definition gderivC (s : C) (x : R) : C := Cmul (Copp s) (Cpw x (Cminus (Copp s) C1)).
Definition gtermC (s : C) (n : nat) : C :=
  Cminus (gC s (INR (S n))) (Cminus (GC s (INR (S (S n)))) (GC s (INR (S n)))).

Lemma Re_Cminus : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros a b; unfold Cminus, Cadd, Copp; cbn [Re]; ring. Qed.

Lemma Im_Cminus : forall a b, Im (Cminus a b) = Im a - Im b.
Proof. intros a b; unfold Cminus, Cadd, Copp; cbn [Im]; ring. Qed.

Lemma exp_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H; destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | rewrite Heq; apply Rle_refl ].
Qed.

(* x^{-e} is antitone in the base for e>=0 *)
Lemma Rpow_negexp_anti : forall x y e, 0 < x -> x <= y -> 0 <= e ->
  Rpower y (- e) <= Rpower x (- e).
Proof.
  intros x y e Hx Hxy He; unfold Rpower; apply exp_le.
  assert (Hln : ln x <= ln y).
  { destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq];
      [ left; apply ln_increasing; [ exact Hx | exact Hlt ] | rewrite Heq; apply Rle_refl ]. }
  apply Rmult_le_compat_neg_l; [ lra | exact Hln ].
Qed.

(* the antiderivative relation  Re/Im (G)' = Re/Im (g), where the Cinv
   factor cancels the (1-s) from the base derivative of x^{1-s} *)
Lemma ReGC_deriv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun t => Re (GC s t)) x (Re (gC s x)).
Proof.
  intros s x Hx Hs; unfold GC, gC.
  replace (Re (Cpw x (Copp s)))
    with (Re (Cmul (Cmul (Cminus C1 s) (Cpw x (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    by (f_equal; replace (Cminus (Cminus C1 s) C1) with (Copp s) by ring; field; exact Hs).
  apply Re_Cmul_deriv; exact Hx.
Qed.

Lemma ImGC_deriv : forall s x, 0 < x -> Cminus C1 s <> C0 ->
  derivable_pt_lim (fun t => Im (GC s t)) x (Im (gC s x)).
Proof.
  intros s x Hx Hs; unfold GC, gC.
  replace (Im (Cpw x (Copp s)))
    with (Im (Cmul (Cmul (Cminus C1 s) (Cpw x (Cminus (Cminus C1 s) C1))) (Cinv (Cminus C1 s))))
    by (f_equal; replace (Cminus (Cminus C1 s) C1) with (Copp s) by ring; field; exact Hs).
  apply Im_Cmul_deriv; exact Hx.
Qed.

Lemma RegC_deriv : forall s x, 0 < x ->
  derivable_pt_lim (fun t => Re (gC s t)) x (Re (gderivC s x)).
Proof. intros s x Hx; unfold gC, gderivC; apply Re_Cpw_deriv; exact Hx. Qed.

Lemma ImgC_deriv : forall s x, 0 < x ->
  derivable_pt_lim (fun t => Im (gC s t)) x (Im (gderivC s x)).
Proof. intros s x Hx; unfold gC, gderivC; apply Im_Cpw_deriv; exact Hx. Qed.

Lemma Cmod_gderivC : forall s x, Cmod (gderivC s x) = Cmod s * Rpower x (- Re s - 1).
Proof.
  intros s x; unfold gderivC; rewrite Cmod_wCpw, Cmod_opp.
  replace (Re (Copp s) - 1) with (- Re s - 1) by (unfold Copp; cbn [Re]; ring).
  reflexivity.
Qed.

Print Assumptions ReGC_deriv.

(* ================================================================= *)
(*  END CZetaTerm.v (part 2).                                          *)
(* ================================================================= *)
