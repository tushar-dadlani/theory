(* ================================================================= *)
(*  CIdentityZero.v  (identity-theorem plan, B2-iterate chain -> B4)   *)
(*                                                                    *)
(*  The identity theorem at the centre 0, from a holomorphic           *)
(*  derivative chain vanishing at 0:                                   *)
(*                                                                    *)
(*    given fseq : nat -> C -> C with fseq(S k) = derivative of fseq k, *)
(*    each continuous and bounded on the circle, and fseq k 0 = 0 for   *)
(*    all k, then  fseq 0 w = 0  for every |w| < R.                     *)
(*                                                                    *)
(*  Proof: the coefficient integrals a_k(i) = oint (fseq i)/z^{k+1}      *)
(*  satisfy  a_0(i) = 2 pi i . (fseq i)(0) = 0   (B1 at w=0) and         *)
(*  a_{Sm}(i) related to a_m(S i) by CDerivCoeff.coeff_recur; induction  *)
(*  on m gives a_m(i) = 0 for all i,m, hence all Taylor coefficients of  *)
(*  fseq 0 vanish, and CTaylorRem.taylor_center_zero closes it.         *)
(*                                                                    *)
(*  Axiom-clean.  (fseq k 0 = 0 -- "all derivatives vanish at 0" -- is   *)
(*  the B5 input, taken here as a hypothesis.)                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        RootsOfUnity CTaylor CTaylorRem CDerivCoeff CWindingOffCenter CCauchyFull.
Open Scope R_scope.

Section ChainZero.
Variable Rr : R.
Variable fseq : nat -> C -> C.
Hypothesis HR : 0 < Rr.
Hypothesis Hchain : forall k z, is_Cderiv (fseq k) z (fseq (S k) z).
Hypothesis Hcc : forall k, CcontC (fseq k).
Hypothesis Hbd : forall k, exists Mf, 0 <= Mf /\ forall u, Cmod (fseq k (arc Rr u)) <= Mf.
Hypothesis Hvanish : forall k, fseq k C0 = C0.

Definition Hhol (k : nat) : forall z, exists d, is_Cderiv (fseq k) z d :=
  fun z => ex_intro _ (fseq (S k) z) (Hchain k z).

(* the coefficient integral  a_j(i) = oint (fseq i)/z^{S j} *)
Definition A (i j : nat) : C :=
  Cintf (pki Rr (fseq i) j) (Hpki Rr (fseq i) HR (Hcc i) j) 0 (2 * PI).

Lemma arc_ne0' : forall u, arc Rr u <> C0.
Proof.
  intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra.
Qed.

(* base:  a_0(i) = oint (fseq i)/z = 2 pi i . (fseq i)(0) = 0  *)
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
  rewrite (Cintf_ext (pki Rr (fseq i) 0)
             (fun u => Cmul (Cmul (fseq i (arc Rr u)) (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))
             (Hpki Rr (fseq i) HR (Hcc i) 0) Hbase0 0 (2 * PI)).
  2:{ intro u. unfold pki. cbn [Cpow].
      replace (Cmul (arc Rr u) C1) with (Cminus (arc Rr u) C0)
        by (apply Ceq; unfold Cmul, Cminus, C1, C0; cbn [Re Im]; ring).
      reflexivity. }
  destruct (Hhol i C0) as [dw Hdw].
  assert (Hw0 : Cmod C0 < Rr) by (rewrite (proj2 (Cmod0 C0) eq_refl); exact HR).
  change (Cintf (fun u =>
            Cmul (Cmul (fseq i (arc Rr u)) (Cinv (Cminus (arc Rr u) C0))) (arc' Rr u))
            Hbase0 0 (2 * PI))
    with (pathint (arc Rr) (arc' Rr)
            (fun z => Cmul (fseq i z) (Cinv (Cminus z C0))) Hbase0 0 (2 * PI)).
  rewrite (cauchy_interior (fseq i) Rr C0 dw (Hhol i) Hdw HR Hw0 Hbase0).
  rewrite (Hvanish i). apply Ceq; unfold Cmul, C0; cbn [Re Im]; ring.
Qed.

(* recurrence:  a_m(S i) = (S m) . a_{S m}(i)   (coeff_recur, kAi=pki, kBi=pki o S) *)
Lemma A_step : forall i m, A (S i) m = Cmul (RtoC (INR (S m))) (A i (S m)).
Proof.
  intros i m. unfold A.
  rewrite (Cintf_irrel (pki Rr (fseq (S i)) m)
             (Hpki Rr (fseq (S i)) HR (Hcc (S i)) m)
             (HcA Rr (fseq (S i)) HR (Hcc (S i)) m) 0 (2 * PI)).
  rewrite (Cintf_irrel (pki Rr (fseq i) (S m))
             (Hpki Rr (fseq i) HR (Hcc i) (S m))
             (HcB Rr (fseq i) HR (Hcc i) m) 0 (2 * PI)).
  exact (coeff_recur Rr (fseq i) (fseq (S i)) HR (Hchain i) (Hcc i) (Hcc (S i)) m).
Qed.

(* induction on the coefficient index: all coefficients vanish *)
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

(* ================================================================= *)
(*  Identity theorem at 0 from a smooth chain vanishing at 0          *)
(* ================================================================= *)
Theorem identity_at_zero : forall w, Cmod w < Rr -> fseq 0 w = C0.
Proof.
  intros w Hw.
  apply (taylor_center_zero Rr (fseq 0) w HR (Hhol 0) (Hcc 0) Hw (Hbd 0)).
  intro k. exact (A_zero k 0).
Qed.

End ChainZero.

Print Assumptions identity_at_zero.
