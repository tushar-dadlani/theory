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

(* ----------------------------------------------------------------- *)
(*  the analytic layer:  two-sided squeeze and square-of-a-limit      *)
(* ----------------------------------------------------------------- *)

(* |z| ≤ b  ⇒  − b ≤ z *)
Lemma abs_le_neg : forall z b : CReal, (CReal_abs z <= b)%CReal -> (- b <= z)%CReal.
Proof.
  intros z b H.
  assert (Hnz : (- z <= b)%CReal).
  { eapply CReal_le_trans; [ | exact H ].
    rewrite <- (CReal_abs_opp z); apply CReal_le_abs. }
  pose proof (CReal_opp_ge_le_contravar b (- z) Hnz) as H2.
  eapply CReal_le_trans; [ exact H2 | ].
  assert (E : (- - z == z)%CReal) by ring; rewrite E; apply CRealLe_refl.
Qed.

(* two-sided squeeze:  lo → L,  hi → L,  lo ≤ u ≤ hi  ⇒  u → L *)
Lemma cvQ_squeeze : forall (lo u hi : nat -> Q) (L : CReal),
  cvQ lo L -> cvQ hi L ->
  (forall n, (lo n <= u n)%Q) -> (forall n, (u n <= hi n)%Q) -> cvQ u L.
Proof.
  intros lo u hi L Hlo Hhi Hlu Huh p.
  destruct (Hlo p) as [N1 H1]; destruct (Hhi p) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia; assert (Hn2 : (N2 <= n)%nat) by lia.
  apply CReal_abs_le; split.
  - apply CReal_le_trans with (inject_Q (lo n) - L).
    + apply abs_le_neg; exact (H1 n Hn1).
    + apply CReal_plus_le_compat; [ apply inject_Q_le; apply Hlu | apply CRealLe_refl ].
  - apply CReal_le_trans with (inject_Q (hi n) - L).
    + apply CReal_plus_le_compat; [ apply inject_Q_le; apply Huh | apply CRealLe_refl ].
    + apply CReal_le_trans with (CReal_abs (inject_Q (hi n) - L));
        [ apply CReal_le_abs | exact (H2 n Hn2) ].
Qed.

(* square of a convergent rational sequence, with a uniform bound 2 *)
Lemma cvQ_sq : forall (a : nat -> Q) (x : CReal),
  cvQ a x -> (forall n, (Qabs (a n) <= 2)%Q) ->
  cvQ (fun n => (a n * a n)%Q) (x * x).
Proof.
  intros a x Ha Hb p.
  destruct (Ha (5 * p)%positive) as [N HN].
  exists N; intros n Hn; cbn beta.
  set (A := inject_Q (a n)); set (d := (A - x)%CReal).
  assert (Hd : (CReal_abs d <= inject_Q (1 # (5 * p)))%CReal) by (unfold d, A; apply HN; exact Hn).
  assert (Egoal : (inject_Q (a n * a n) - x * x == (A + x) * d)%CReal)
    by (unfold d, A; rewrite inject_Q_mult; ring).
  rewrite Egoal, CReal_abs_mult.
  assert (Hx : (CReal_abs x <= CReal_abs A + CReal_abs d)%CReal).
  { assert (Ex : (x == A + - d)%CReal) by (unfold d; ring).
    rewrite Ex; eapply CReal_le_trans; [ apply CReal_abs_triang | ].
    rewrite CReal_abs_opp; apply CRealLe_refl. }
  assert (HA2 : (CReal_abs A <= inject_Q 2)%CReal) by (unfold A; apply inj_abs_le, Hb).
  assert (Hd1 : (CReal_abs d <= inject_Q 1)%CReal)
    by (eapply CReal_le_trans; [ exact Hd | apply inject_Q_le; unfold Qle; simpl; lia ]).
  assert (HAx : (CReal_abs (A + x) <= inject_Q 5)%CReal).
  { eapply CReal_le_trans; [ apply CReal_abs_triang | ].
    eapply CReal_le_trans; [ apply CReal_plus_le_compat_l; exact Hx | ].
    eapply CReal_le_trans;
      [ apply CReal_plus_le_compat; [ exact HA2 | apply CReal_plus_le_compat; [ exact HA2 | exact Hd1 ] ] | ].
    rewrite <- inject_Q_plus, <- inject_Q_plus; apply inject_Q_le; unfold Qle; simpl; lia. }
  eapply CReal_le_trans; [ apply CReal_mult_le_compat_r; [ apply CReal_abs_pos | exact HAx ] | ].
  eapply CReal_le_trans;
    [ apply CReal_mult_le_compat_l; [ apply inject_Q_le; unfold Qle; simpl; lia | exact Hd ] | ].
  rewrite <- inject_Q_mult; apply inject_Q_le; unfold Qle; simpl; lia.
Qed.

(* ================================================================= *)
(*  END CRealCv.v                                                    *)
(*  cvQ + cvQ_of_regular (the axiom-free completeness bridge) +       *)
(*  eventually_eq + reindex + cvQ_squeeze + cvQ_sq.                   *)
(* ================================================================= *)
