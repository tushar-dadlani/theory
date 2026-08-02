(* ================================================================= *)
(*  Cmodulus.v  —  the complex modulus |·| on the algebraic field C.  *)
(*                                                                    *)
(*  Cmod c := sqrt (Cnorm2 c).  Establishes the metric groundwork     *)
(*  (nonneg, multiplicativity, Cauchy–Schwarz, triangle inequality)   *)
(*  for the complex-analysis layer.  Axiom-clean.                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField.
Open Scope R_scope.

Definition Cmod (c : C) : R := sqrt (Cnorm2 c).

Lemma Cmod_nonneg : forall c, 0 <= Cmod c.
Proof. intro c; apply sqrt_pos. Qed.

Lemma Cmod_sqr : forall c, Rsqr (Cmod c) = Cnorm2 c.
Proof. intro c; unfold Cmod, Rsqr; apply sqrt_sqrt, Cnorm2_nonneg. Qed.

Lemma Cnorm2_mul : forall a b, Cnorm2 (Cmul a b) = Cnorm2 a * Cnorm2 b.
Proof. intros a b; unfold Cnorm2, Cmul; simpl; ring. Qed.

Lemma Cmod_mul : forall a b, Cmod (Cmul a b) = Cmod a * Cmod b.
Proof.
  intros a b; unfold Cmod; rewrite Cnorm2_mul, sqrt_mult_alt by apply Cnorm2_nonneg; reflexivity.
Qed.

Lemma Cmod_RtoC : forall r, Cmod (RtoC r) = Rabs r.
Proof.
  intro r; unfold Cmod, Cnorm2, RtoC; simpl.
  replace (r * r + 0 * 0) with (Rsqr r) by (unfold Rsqr; ring). apply sqrt_Rsqr_abs.
Qed.

Lemma Cmod0 : forall c, Cmod c = 0 <-> c = C0.
Proof.
  intro c; unfold Cmod; split.
  - intro H. assert (HN : Re c * Re c + Im c * Im c = 0).
    { pose proof (Cnorm2_nonneg c) as Hnn.
      apply (sqrt_eq_0 (Cnorm2 c) Hnn) in H; unfold Cnorm2 in H; exact H. }
    apply Ceq; simpl.
    + apply Rsqr_0_uniq; unfold Rsqr.
      pose proof (Rle_0_sqr (Re c)); pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; lra.
    + apply Rsqr_0_uniq; unfold Rsqr.
      pose proof (Rle_0_sqr (Re c)); pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; lra.
  - intro H; subst c; unfold Cnorm2, C0; simpl.
    replace (0 * 0 + 0 * 0) with 0 by ring; apply sqrt_0.
Qed.

Lemma Cmod_CauchySchwarz : forall a b, Re a * Re b + Im a * Im b <= Cmod a * Cmod b.
Proof.
  intros a b.
  unfold Cmod; rewrite <- sqrt_mult_alt by apply Cnorm2_nonneg.
  destruct (Rle_dec (Re a * Re b + Im a * Im b) 0) as [Hs | Hs].
  - apply Rle_trans with 0; [ exact Hs | apply sqrt_pos ].
  - apply Rnot_le_lt in Hs.
    rewrite <- (sqrt_Rsqr (Re a * Re b + Im a * Im b)) by lra.
    apply sqrt_le_1_alt. unfold Rsqr, Cnorm2.
    pose proof (Rle_0_sqr (Re a * Im b - Im a * Re b)) as HSOS; unfold Rsqr in HSOS. nra.
Qed.

Lemma Cmod_triangle : forall a b, Cmod (Cadd a b) <= Cmod a + Cmod b.
Proof.
  intros a b.
  apply Rsqr_incr_0_var;
    [ | apply Rplus_le_le_0_compat; apply Cmod_nonneg ].
  rewrite Rsqr_plus, !Cmod_sqr.
  pose proof (Cmod_CauchySchwarz a b) as HCS.
  unfold Cnorm2, Cadd; simpl. nra.
Qed.

Lemma Cmod_conj : forall a, Cmod (Cconj a) = Cmod a.
Proof. intro a; unfold Cmod, Cnorm2, Cconj; simpl; f_equal; ring. Qed.

Lemma Cmod_opp : forall a, Cmod (Copp a) = Cmod a.
Proof. intro a; unfold Cmod, Cnorm2, Copp; simpl; f_equal; ring. Qed.

Print Assumptions Cmod_triangle.

(* ================================================================= *)
(*  END Cmodulus.v.                                                   *)
(* ================================================================= *)
