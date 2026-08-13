(* ================================================================= *)
(*  CIdentityZeroDom.v  (identity-theorem plan, DOMAIN-RESTRICTED chain)*)
(*                                                                    *)
(*  identity_at_zero_D: the identity theorem at 0 from a derivative     *)
(*  chain that is differentiable only on the disk |z| < R+1 and          *)
(*  pointwise-continuous everywhere (Fptc), vanishing at 0.  Same as     *)
(*  CIdentityZero.identity_at_zero, with cauchy_interior -> _dom,        *)
(*  coeff_recur -> _D, taylor_center_zero -> _D.  Axiom-clean.          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        RootsOfUnity CTaylor CTaylorRemDom CDerivCoeffDom CRemovableExtDom
        CWindingOffCenter PerronRemovable.
Open Scope R_scope.

Section ChainZeroDom.
Variable Rr : R.
Variable fseq : nat -> C -> C.
Hypothesis HR : 0 < Rr.
Hypothesis Hchain_disk : forall k z, Cmod z < Rr + 1 -> is_Cderiv (fseq k) z (fseq (S k) z).
Hypothesis Fptc : forall k z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (fseq k z') (fseq k z)) < eps.
Hypothesis Hbd : forall k, exists Mf, 0 <= Mf /\ forall u, Cmod (fseq k (arc Rr u)) <= Mf.
Hypothesis Hvanish : forall k, fseq k C0 = C0.

Definition Hcc (k : nat) : CcontC (fseq k) := ptcont_CcontC (fseq k) (Fptc k).
Definition Hhol_disk (k : nat) :
  forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv (fseq k) z d :=
  fun z Hz => ex_intro _ (fseq (S k) z) (Hchain_disk k z Hz).

Definition A (i j : nat) : C :=
  Cintf (pki_D Rr (fseq i) j) (Hpki_D Rr (fseq i) HR (Fptc i) j) 0 (2 * PI).

Lemma arc_ne0' : forall u, arc Rr u <> C0.
Proof.
  intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra.
Qed.

Lemma A_base : forall i, A i 0 = C0.
Proof.
  intro i. unfold A.
  assert (Hbase0 : Ccont (fun u =>
    Cmul (Cmul (fseq i (arc Rr u)) (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))).
  { apply Ccont_mul; [ | apply Ccont_arc' ].
    apply Ccont_mul; [ exact (Hcc i (arc Rr) (Ccont_arc Rr)) | ].
    apply Ccont_inv; [ apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ] | ].
    intros u Hc. apply (arc_ne0' u). rewrite <- Hc.
    apply Ceq; unfold Cminus, C0; cbn [Re Im]; ring. }
  rewrite (Cintf_ext (pki_D Rr (fseq i) 0)
             (fun u => Cmul (Cmul (fseq i (arc Rr u)) (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))
             (Hpki_D Rr (fseq i) HR (Fptc i) 0) Hbase0 0 (2 * PI)).
  2:{ intro u. unfold pki_D. cbn [Cpow].
      replace (Cmul (arc Rr u) C1) with (Cminus (arc Rr u) C0)
        by (apply Ceq; unfold Cmul, Cminus, C1, C0; cbn [Re Im]; ring).
      reflexivity. }
  destruct (Hhol_disk i C0 ltac:(rewrite (proj2 (Cmod0 C0) eq_refl); lra)) as [dw Hdw].
  assert (Hw0 : Cmod C0 < Rr) by (rewrite (proj2 (Cmod0 C0) eq_refl); exact HR).
  change (Cintf (fun u =>
            Cmul (Cmul (fseq i (arc Rr u)) (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))
            Hbase0 0 (2 * PI))
    with (pathint (arc Rr) (arc' Rr)
            (fun z => Cmul (fseq i z) (Cinv (Cminus z C0))) Hbase0 0 (2 * PI)).
  rewrite (cauchy_interior_dom (fseq i) Rr C0 dw HR Hw0 Hdw (Fptc i)
             (fun z Hz (_ : z <> C0) => Hhol_disk i z Hz) Hbase0).
  rewrite (Hvanish i). apply Ceq; unfold Cmul, C0; cbn [Re Im]; ring.
Qed.

Lemma A_step : forall i m, A (S i) m = Cmul (RtoC (INR (S m))) (A i (S m)).
Proof.
  intros i m. unfold A.
  rewrite (Cintf_irrel (pki_D Rr (fseq (S i)) m)
             (Hpki_D Rr (fseq (S i)) HR (Fptc (S i)) m)
             (HcA_D Rr (fseq (S i)) HR (Hcc (S i)) m) 0 (2 * PI)).
  rewrite (Cintf_irrel (pki_D Rr (fseq i) (S m))
             (Hpki_D Rr (fseq i) HR (Fptc i) (S m))
             (HcB_D Rr (fseq i) HR (Hcc i) m) 0 (2 * PI)).
  exact (coeff_recur_D Rr (fseq i) (fseq (S i)) HR (Hchain_disk i) (Hcc i) (Hcc (S i)) m).
Qed.

Lemma A_zero : forall m i, A i m = C0.
Proof.
  induction m as [|m IH]; intro i.
  - apply A_base.
  - assert (Hs := A_step i m).
    rewrite (IH (S i)) in Hs.
    symmetry in Hs.
    apply (Cmul_eq0_l (RtoC (INR (S m))) (A i (S m))); [ | exact Hs ].
    intro Hc. assert (Hpos : 0 < INR (S m)) by (apply lt_0_INR; lia).
    apply (f_equal Re) in Hc. unfold RtoC, C0 in Hc; cbn [Re] in Hc. lra.
Qed.

Theorem identity_at_zero_D : forall w, Cmod w < Rr -> fseq 0 w = C0.
Proof.
  intros w Hw.
  apply (taylor_center_zero_D Rr (fseq 0) w HR (Hhol_disk 0) (Fptc 0) Hw (Hbd 0)).
  intro k. exact (A_zero k 0).
Qed.

End ChainZeroDom.

Print Assumptions identity_at_zero_D.
