(* ================================================================= *)
(*  Ell2Partition.v   (the primon-gas partition function is zeta)        *)
(*                                                                    *)
(*  On the one-particle Hilbert space l^2, the log-Hamiltonian          *)
(*     H = diag(log n)   (Ell2Zeta.Hlog)                               *)
(*  generates the heat semigroup  e^{-b H} = diag(n^{-b})  (Ell2Zeta.z),*)
(*  whose spectral (diagonal) trace is the primon-gas partition         *)
(*  function.  This file bundles the link                              *)
(*                                                                    *)
(*     Tr_N(e^{-b H}) = sum_{n=1}^N e^{-b log n} = sum_{n=1}^N n^{-b}   *)
(*                    ---> zeta(b)         (converges for b > 1)         *)
(*                                                                    *)
(*  as a single theorem.  The convergence for b>1 comes from            *)
(*  HagedornTransition.Zpart_cv (monotone + bounded), a wider range      *)
(*  than Ell2ZetaConverge (which only reaches s >= 2).                  *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Rpower Lra Lia List.
Require Import Ell2 Ell2Operator Ell2Zeta Ell2ZetaConverge HagedornTransition.
Open Scope R_scope.

Lemma Un_cv_ext' : forall (u v : nat -> R) l,
  (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof.
  intros u v l H Hu eps He. destruct (Hu eps He) as [N HN]. exists N.
  intros n Hn. rewrite <- H. apply HN; exact Hn.
Qed.

(* the operator's partial trace  sum_{n=1}^{S N} n^{-b}  is the Hagedorn
   partition function  Zpart b N = sum_{k=0}^N (k+1)^{-b}. *)
Lemma dzeta_eq_Zpart : forall b N, dzeta b (S N) = Zpart b N.
Proof.
  intros b N. induction N as [| N IH].
  - rewrite dzeta_succ. replace (dzeta b 0) with 0 by reflexivity.
    rewrite Rplus_0_l. unfold Zpart, z. reflexivity.
  - rewrite dzeta_succ, IH. unfold Zpart; rewrite tech5. reflexivity.
Qed.

(* the diagonal trace of e^{-bH} converges for b > 1  (= zeta(b)). *)
Theorem dzeta_cv : forall b, 1 < b -> { l : R | Un_cv (dzeta b) l }.
Proof.
  intros b Hb. destruct (Zpart_cv b Hb) as [l Hl]. exists l.
  apply Un_cv_unshift.
  apply (Un_cv_ext' (Zpart b)); [ intro M; symmetry; apply dzeta_eq_Zpart | exact Hl ].
Qed.

(* the N-th partial trace is literally  Tr_N(e^{-bH}) = sum_{n=1}^N e^{-b log n}. *)
Lemma heat_trace_eq : forall b N,
  diag_trace (z b) N = diag_trace (fun n => exp ((- b) * Hlog n)) N.
Proof.
  intros b N. rewrite !diag_trace_eq. f_equal.
  apply map_ext_in. intros n Hn. apply in_seq in Hn.
  apply zeta_is_exp_neg_sH. lia.
Qed.

(* ------------------------------------------------------------------ *)
(*  the bundled statement:  the heat-semigroup partition function        *)
(*  Tr(e^{-bH}) converges (to zeta(b)) for b > 1.                        *)
(* ------------------------------------------------------------------ *)

Theorem partition_function_is_zeta : forall b, 1 < b ->
  { Z : R |
    (* the spectral trace of the zeta-operator e^{-bH} = diag(n^{-b}) converges *)
    Un_cv (fun N => diag_trace (z b) N) Z /\
    (* and each partial trace is exactly  Tr_N(e^{-bH}) = sum_{n=1}^N e^{-b log n} *)
    (forall N, diag_trace (z b) N = diag_trace (fun n => exp ((- b) * Hlog n)) N) }.
Proof.
  intros b Hb. destruct (dzeta_cv b Hb) as [Z HZ]. exists Z. split.
  - apply (Un_cv_ext' (dzeta b)); [ intro N; symmetry; apply zeta_partition | exact HZ ].
  - intro N; apply heat_trace_eq.
Qed.

(* the same limit in explicit heat-trace form:  Tr_N(e^{-bH}) -> zeta(b). *)
Corollary heat_partition_converges : forall b, 1 < b ->
  { Z : R | Un_cv (fun N => diag_trace (fun n => exp ((- b) * Hlog n)) N) Z }.
Proof.
  intros b Hb. destruct (partition_function_is_zeta b Hb) as [Z [HZ Heq]].
  exists Z. apply (Un_cv_ext' (fun N => diag_trace (z b) N));
    [ exact Heq | exact HZ ].
Qed.

Print Assumptions partition_function_is_zeta.
