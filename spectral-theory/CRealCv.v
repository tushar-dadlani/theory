(* ================================================================= *)
(*  CRealCv.v                                                        *)
(*                                                                    *)
(*  An AXIOM-FREE convergence calculus on Rocq's constructive reals.  *)
(*                                                                    *)
(*  The classical `Reals` are the constructive `CReal`               *)
(*  (Reals.Cauchy.ConstructiveCauchyReals) QUOTIENTED by the three    *)
(*  classical axioms (sig_forall_dec, sig_not_dec,                    *)
(*  functional_extensionality_dep).  The `CReal` layer underneath is  *)
(*  axiom-free.  This file works directly over `CReal` and defines a  *)
(*  convergence notion for a RATIONAL sequence toward a `CReal`,      *)
(*                                                                    *)
(*     cvQ a x  :=  ∀p, ∃N, ∀n≥N, |inject_Q (a n) − x| ≤ 1/p ,       *)
(*                                                                    *)
(*  with the key bridge `cvQ_of_regular`: a rational sequence with    *)
(*  an explicit Cauchy modulus HAS a CReal limit (via the stdlib      *)
(*  `CRealComplete`).  This is the constructive replacement for the   *)
(*  classical monotone-bounded convergence (`growing_cv`) that puts   *)
(*  the classical axioms into the ζ(2) arc.  AXIOM-FREE.             *)
(* ================================================================= *)

From Stdlib Require Import QArith Qabs Lqa Lia List Arith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
Open Scope CReal_scope.

(* ----------------------------------------------------------------- *)
(*  the rational→CReal absolute-value bridge                          *)
(* ----------------------------------------------------------------- *)
Lemma inj_abs_le : forall q r : Q, (Qabs q <= r)%Q ->
  (CReal_abs (inject_Q q) <= inject_Q r)%CReal.
Proof.
  intros q r H; apply Qabs_Qle_condition in H; destruct H as [H1 H2].
  apply CReal_abs_le; split.
  - rewrite <- opp_inject_Q; apply inject_Q_le; exact H1.
  - apply inject_Q_le; exact H2.
Qed.

(* inject_Q turns a rational difference into the CReal difference *)
Lemma inject_Q_diff : forall a b : Q,
  (inject_Q (a - b) == inject_Q a + - inject_Q b)%CReal.
Proof.
  intros a b; unfold Qminus; rewrite inject_Q_plus, opp_inject_Q; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  convergence of a rational sequence to a CReal                     *)
(* ----------------------------------------------------------------- *)
Definition cvQ (a : nat -> Q) (x : CReal) : Prop :=
  forall p : positive, exists N : nat,
    forall n : nat, (N <= n)%nat -> (CReal_abs (inject_Q (a n) - x) <= inject_Q (1 # p))%CReal.

(* THE BRIDGE: a rational sequence with an explicit Cauchy modulus has a limit. *)
Lemma cvQ_of_regular : forall (a : nat -> Q),
  (forall p : positive, {N : nat |
      forall i j, (N <= i)%nat -> (N <= j)%nat -> (Qabs (a i - a j) <= 1 # p)%Q}) ->
  { x : CReal & cvQ a x }.
Proof.
  intros a Hmod.
  assert (Hcm : forall p : positive, {n : nat |
      forall i j, (n <= i)%nat -> (n <= j)%nat ->
        (CReal_abs (inject_Q (a i) + - inject_Q (a j)) <= inject_Q (1 # p))%CReal}).
  { intro p; destruct (Hmod p) as [N HN]; exists N; intros i j Hi Hj.
    rewrite <- (inject_Q_diff (a i) (a j)); apply inj_abs_le; apply HN; assumption. }
  destruct (CRealComplete (fun n => inject_Q (a n)) Hcm) as [l Hl].
  exists l; intro p; destruct (Hl p) as [n Hn]; exists n; intros m Hm.
  apply Hn; exact Hm.
Qed.

(* eventually-equal rational sequences share a limit *)
Lemma cvQ_eventually_eq : forall (a b : nat -> Q) (x : CReal) (K : nat),
  (forall n, (K <= n)%nat -> (a n == b n)%Q) -> cvQ b x -> cvQ a x.
Proof.
  intros a b x K Heq Hb p; destruct (Hb p) as [N HN].
  exists (Nat.max N K); intros n Hn.
  assert (E : (inject_Q (a n) == inject_Q (b n))%CReal)
    by (apply inject_Q_morph, Heq; lia).
  rewrite E; apply HN; lia.
Qed.

(* reindexing along a divergent index map preserves the limit *)
Lemma cvQ_reindex : forall (a : nat -> Q) (x : CReal) (phi : nat -> nat),
  cvQ a x ->
  (forall m, exists K, forall n, (K <= n)%nat -> (m <= phi n)%nat) ->
  cvQ (fun n => a (phi n)) x.
Proof.
  intros a x phi Ha Hdiv p; destruct (Ha p) as [N HN]; destruct (Hdiv N) as [K HK].
  exists K; intros n Hn; apply HN, HK; exact Hn.
Qed.

(* ================================================================= *)
(*  END CRealCv.v                                                    *)
(*  cvQ + cvQ_of_regular (the axiom-free completeness bridge) +       *)
(*  eventually_eq + reindex.  (Product-of-limits and the monotone     *)
(*  ≤-limit / squeeze lemmas are deferred to the ζ² milestone.)       *)
(* ================================================================= *)
