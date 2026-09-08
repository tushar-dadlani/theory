(* ================================================================= *)
(*  CLHolo1.v  --  L(s,chi) as a total function, and its partial       *)
(*  sums as entire functions of s.                                    *)
(*                                                                    *)
(*  Step one toward differentiability of L on Re s > 0, which is what  *)
(*  L(1+it,chi) <> 0 actually needs: the sequence argument bounds      *)
(*  |L(sigma+it0)| = |L(sigma+it0) - L(1+it0)| <= C (sigma - 1) at a   *)
(*  putative zero, and that is a statement AT the boundary line, not   *)
(*  inside Re s > 1.                                                   *)
(*                                                                    *)
(*  Unlike the zeta case there is no clamp needed here: each partial   *)
(*  sum is a finite combination of s |-> n^{-s} = Cexpf(-s ln n),      *)
(*  which is ENTIRE.  The clamp will only be needed for the limit.     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List.
Require Import ComplexField Cmodulus CexpFull CPower CPowMul CSeries CDeriv
        Holomorphic RootsOfUnity ZmodOrder DirichletModP CZetaTerm
        CharModulus CTwistedCoeff CLSeries CCharSumBound CLContinue.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  1.  s |-> n^{-s} is entire, with derivative -ln n * n^{-s}         *)
(* ----------------------------------------------------------------- *)

Lemma gC_sderiv_loc : forall (x : R) (s : C), 0 < x ->
  is_Cderiv (fun w => gC w x) s
            (Cmul (Copp C1) (Cmul (RtoC (ln x)) (Cpw x (Copp s)))).
Proof.
  intros x s Hx. unfold gC.
  apply (is_Cderiv_ext (fun w => Cpw x (Cadd (Cmul (Copp C1) w) C0))).
  - intro w; f_equal; ring.
  - apply (Cderiv_comp_affine (fun v => Cpw x v) (Copp C1) C0 s
             (Cmul (RtoC (ln x)) (Cpw x (Copp s)))).
    replace (Cadd (Cmul (Copp C1) s) C0) with (Copp s) by ring.
    apply Cpw_deriv; exact Hx.
Qed.

(* one term of the L-series, differentiated in s *)
Definition Ldterm (p g A : nat) (s : C) (k : nat) : C :=
  Cmul (dchar p g A (S k))
       (Cmul (Copp C1) (Cmul (RtoC (ln (INR (S k)))) (Cpw (INR (S k)) (Copp s)))).

Lemma Lterm_sderiv : forall p g A s k,
  is_Cderiv (fun w => Lterm p g A w k) s (Ldterm p g A s k).
Proof.
  intros p g A s k.
  assert (Hx : 0 < INR (S k)) by (apply lt_0_INR; lia).
  set (dG := Cmul (Copp C1)
                  (Cmul (RtoC (ln (INR (S k)))) (Cpw (INR (S k)) (Copp s)))).
  replace (Ldterm p g A s k)
    with (Cadd (Cmul C0 (Cpw (INR (S k)) (Copp s)))
               (Cmul (dchar p g A (S k)) dG))
    by (unfold Ldterm, dG; ring).
  unfold Lterm, Gchi.
  apply (Cderiv_mul (fun _ => dchar p g A (S k))
                    (fun w => Cpw (INR (S k)) (Copp w)) s C0 dG).
  - apply Cderiv_const.
  - unfold dG. exact (gC_sderiv_loc (INR (S k)) s Hx).
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  the partial sums are entire                                    *)
(* ----------------------------------------------------------------- *)

Definition Lpart (p g A n : nat) (s : C) : C := Cpsum (Lterm p g A s) n.
Definition Ldpart (p g A n : nat) (s : C) : C := Cpsum (Ldterm p g A s) n.

Lemma Lpart_holo : forall p g A n s,
  is_Cderiv (Lpart p g A n) s (Ldpart p g A n s).
Proof.
  intros p g A n s. induction n as [| n IH].
  - unfold Lpart, Ldpart; cbn [Cpsum]. apply Lterm_sderiv.
  - unfold Lpart, Ldpart in *; cbn [Cpsum].
    apply Cderiv_add; [ exact IH | apply Lterm_sderiv ].
Qed.

Corollary Lpart_holo_ex : forall p g A n s,
  exists d, is_Cderiv (Lpart p g A n) s d.
Proof. intros; eexists; apply Lpart_holo. Qed.

(* ----------------------------------------------------------------- *)
(*  3.  L as a total function on Re s > 0                              *)
(* ----------------------------------------------------------------- *)

Section Total.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.

Definition LFun (s : C) : C :=
  match Rlt_dec 0 (Re s) with
  | left h => proj1_sig (Lterm_cv_halfplane p g A Hp Hg Hord HA s h)
  | right _ => C0
  end.

Lemma LFun_series : forall s, 0 < Re s -> Cseries_cv (Lterm p g A s) (LFun s).
Proof.
  intros s Hs. unfold LFun.
  destruct (Rlt_dec 0 (Re s)) as [h | h]; [ | exfalso; lra ].
  exact (proj2_sig (Lterm_cv_halfplane p g A Hp Hg Hord HA s h)).
Qed.

(* the value does not depend on which convergence proof produced it *)
Lemma LFun_unique : forall s L, 0 < Re s ->
  Cseries_cv (Lterm p g A s) L -> L = LFun s.
Proof.
  intros s L Hs HL.
  apply (CUn_cv_unique (Cpsum (Lterm p g A s)));
    [ exact HL | apply LFun_series; exact Hs ].
Qed.

(* NOTE.  Agreement with CLSeries.LC on Re s > 1 follows from LFun_unique
   applied to L_is_series; not stated separately because LC carries its own
   proof-term arguments and the reconciliation is never needed in that form. *)

End Total.

Print Assumptions Lpart_holo.
Print Assumptions LFun_series.

(* ================================================================= *)
(*  END CLHolo1.v                                                     *)
(* ================================================================= *)
