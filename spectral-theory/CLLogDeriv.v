(* ================================================================= *)
(*  CLLogDeriv.v  --  L'(s,chi) = - Phi(s,chi) L(s,chi)  on Re s > 1. *)
(*                                                                    *)
(*  i.e.  -L'/L = sum Lambda(n) chi(n) n^{-s},  the log-derivative     *)
(*  identity, with no complex logarithm anywhere.                     *)
(*                                                                    *)
(*  Nothing new is proved: this is the join of                        *)
(*    CVonMangoldtLChi.phi_L_eq  (Phi L = sum chi(n) ln n n^{-s})     *)
(*    CLDeriv.LFun_deriv         (LFun' = sum of termwise derivatives) *)
(*  and the only content is that the two are stated in different       *)
(*  summation conventions -- Cls (seq 1 N) for the Dirichlet-product   *)
(*  machinery, Cpsum for the series machinery -- bridged by            *)
(*  CDirichlet.Cpsum_shift_eq_Cls, plus the sign (Ldterm carries the   *)
(*  Copp that makes it a DERIVATIVE rather than the ln-weighted term). *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus Holomorphic CexpFull CSeries CListSum
        CDirichlet RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff
        CLSeries CLHolo1 CVonMangoldtChi CVonMangoldtLChi CLDeriv.
Import ListNotations.
Open Scope R_scope.

Lemma CUn_cv_opp : forall u l, CUn_cv u l -> CUn_cv (fun n => Copp (u n)) (Copp l).
Proof.
  intros u l H eps He. destruct (H eps He) as [N HN].
  exists N. intros n Hn.
  replace (Cminus (Copp (u n)) (Copp l)) with (Copp (Cminus (u n) l))
    by (apply Ceq; unfold Cminus, Cadd, Copp; cbn [Re Im]; ring).
  rewrite Cmod_opp. apply HN. exact Hn.
Qed.

Lemma CUn_cv_shift : forall u l, CUn_cv u l -> CUn_cv (fun N => u (S N)) l.
Proof.
  intros u l H eps He. destruct (H eps He) as [N HN].
  exists N. intros n Hn. apply HN. lia.
Qed.

Lemma Cpsum_opp : forall F N, Cpsum (fun k => Copp (F k)) N = Copp (Cpsum F N).
Proof.
  intros F N. induction N as [| N IH]; [ reflexivity | ].
  replace (Cpsum (fun k => Copp (F k)) (S N))
    with (Cadd (Cpsum (fun k => Copp (F k)) N) (Copp (F (S N)))) by reflexivity.
  replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
  rewrite IH. apply Ceq; unfold Cadd, Copp; cbn [Re Im]; ring.
Qed.

Lemma Cpsum_ext : forall F G N, (forall k, F k = G k) -> Cpsum F N = Cpsum G N.
Proof.
  intros F G N H. induction N as [| N IH]; [ apply H | ].
  replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
  replace (Cpsum G (S N)) with (Cadd (Cpsum G N) (G (S N))) by reflexivity.
  rewrite IH, (H (S N)). reflexivity.
Qed.

Section LogDeriv.

Variable p g A : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Hypothesis HA : (0 < A < p - 1)%nat.
Variable s : C.
Hypothesis Hs : 1 < Re s.

Notation PH := (Phichi p g A Hg Hord s Hs).
Notation LL := (LFun p g A Hp Hg Hord HA s).

Lemma Hs0 : 0 < Re s. Proof. lra. Qed.

(* the termwise derivative is minus the ln-weighted term *)
Lemma Ldterm_eq : forall k,
  Ldterm p g A s k = Copp (Cmul (RtoC (ln (INR (S k)))) (Gchi p g A s (S k))).
Proof.
  intro k. unfold Ldterm, Gchi.
  apply Ceq; unfold Cmul, Copp, C1, RtoC; cbn [Re Im]; ring.
Qed.

Theorem Ldterm_cv : Cseries_cv (Ldterm p g A s) (Copp (Cmul PH LL)).
Proof.
  unfold Cseries_cv.
  apply (CUn_cv_ext
           (fun N => Copp (Cls (seq 1 (S N))
                      (fun n => Cmul (RtoC (ln (INR n))) (Gchi p g A s n))))).
  - intro N.
    rewrite <- Cpsum_shift_eq_Cls, <- Cpsum_opp.
    apply Cpsum_ext. intro k. symmetry. apply Ldterm_eq.
  - apply CUn_cv_opp.
    apply (CUn_cv_shift (fun N => Cls (seq 1 N)
             (fun n => Cmul (RtoC (ln (INR n))) (Gchi p g A s n)))).
    apply (phi_L_eq p g A Hp Hg Hord s Hs LL).
    apply (LFun_series p g A Hp Hg Hord HA s Hs0).
Qed.

(* ---- THE log-derivative identity ---- *)
Theorem LFun_logderiv :
  is_Cderiv (LFun p g A Hp Hg Hord HA) s (Copp (Cmul PH LL)).
Proof.
  apply (LFun_deriv p g A Hp Hg Hord HA s Hs). exact Ldterm_cv.
Qed.

End LogDeriv.

Print Assumptions LFun_logderiv.

(* ================================================================= *)
(*  END CLLogDeriv.v                                                  *)
(* ================================================================= *)
