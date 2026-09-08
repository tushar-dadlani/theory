(* ================================================================= *)
(*  CTwistedCoeff.v  --  the twisted coefficient chi(n) n^{-s}.        *)
(*                                                                    *)
(*  The Dirichlet L-function's coefficient, in the two indexings the   *)
(*  machinery needs: Fchi on Z (for the Euler-product reindex, whose   *)
(*  codes are integers) and Gchi on nat (for the Dirichlet series).    *)
(*                                                                    *)
(*  Fchi is completely multiplicative on the positives because both    *)
(*  of its factors are: chi by DirichletLEuler.dchar_mul, and          *)
(*  m |-> m^{-s} by CPowMul.Cpw_base_mul.  That is exactly the         *)
(*  hypothesis CEulerReindexGen.Ceuler_reindex_gen asks for.           *)
(*                                                                    *)
(*  And |chi(m) m^{-s}| <= m^{-Re s}, with equality off the modulus    *)
(*  and 0 on it -- an INEQUALITY, not the equality that the zeta case  *)
(*  enjoys.  That asymmetry is what forces the majorant form of the    *)
(*  inclusion-difference bound later on.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CPowMul RootsOfUnity
        Ell2Zeta ZmodOrder DirichletModP DirichletLEuler CharModulus
        CEulerProductFull.
Open Scope R_scope.

Section Twist.

Variable p g a : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Variable s : C.

Definition Gchi (m : nat) : C := Cmul (dchar p g a m) (Cpw (INR m) (Copp s)).
Definition Fchi (n : Z) : C := Cmul (dchar p g a (Z.to_nat n)) (Cpw (IZR n) (Copp s)).

Lemma Re_Copp_s : Re (Copp s) = - Re s.
Proof. unfold Copp; cbn [Re]; ring. Qed.

Lemma Fchi_1 : Fchi 1%Z = C1.
Proof.
  unfold Fchi. change (Z.to_nat 1) with 1%nat.
  rewrite (dchar_1 p g a Hp Hg Hord), Cpw_one. ring.
Qed.

Lemma Fchi_mul : forall u v, (0 < u)%Z -> (0 < v)%Z ->
  Fchi (u * v)%Z = Cmul (Fchi u) (Fchi v).
Proof.
  intros u v Hu Hv. unfold Fchi.
  rewrite Z2Nat.inj_mul by lia.
  rewrite (dchar_mul p g a _ _ Hp Hg Hord).
  rewrite mult_IZR.
  rewrite (Cpw_base_mul (IZR u) (IZR v) (Copp s)
             ltac:(apply IZR_lt; lia) ltac:(apply IZR_lt; lia)).
  ring.
Qed.

Lemma Fchi_nat : forall m, Fchi (Z.of_nat m) = Gchi m.
Proof.
  intro m. unfold Fchi, Gchi. rewrite Nat2Z.id, <- INR_IZR_INZ. reflexivity.
Qed.

(* the majorant: |chi(m) m^{-s}| <= m^{-Re s}, with 0 on the modulus *)
Lemma Gchi_mod_le : forall m, Cmod (Gchi m) <= z (Re s) m.
Proof.
  intro m. unfold Gchi, z.
  rewrite Cmod_mul, Cpw_mod, Re_Copp_s.
  assert (Hpow : 0 < Rpower (INR m) (- Re s))
    by (unfold Rpower; apply exp_pos).
  destruct (Nat.eqb m 0) eqn:E.
  - apply Nat.eqb_eq in E; subst m.
    rewrite (dchar_zero p g a 0%nat ltac:(exists 0%nat; lia)).
    rewrite (proj2 (Cmod0 C0) eq_refl). lra.
  - pose proof (Cmod_dchar_le p g a m) as Hd.
    pose proof (Cmod_nonneg (dchar p g a m)) as Hd0.
    nra.
Qed.

Lemma Fchi_mod_q0 : 0 <= Re s -> forall q, 2 <= IZR q ->
  Cmod (Fchi q) <= Rpower 2 (- Re s).
Proof.
  intros Hs q Hq. unfold Fchi.
  rewrite Cmod_mul, Cpw_mod, Re_Copp_s.
  assert (Hb : Rpower (IZR q) (- Re s) <= Rpower 2 (- Re s))
    by (apply Rpower_base_le; lra).
  assert (Hpos : 0 < Rpower (IZR q) (- Re s))
    by (unfold Rpower; apply exp_pos).
  pose proof (Cmod_dchar_le p g a (Z.to_nat q)) as Hd.
  pose proof (Cmod_nonneg (dchar p g a (Z.to_nat q))) as Hd0.
  nra.
Qed.

End Twist.

Print Assumptions Fchi_mul.
Print Assumptions Gchi_mod_le.

(* ================================================================= *)
(*  END CTwistedCoeff.v                                               *)
(* ================================================================= *)
