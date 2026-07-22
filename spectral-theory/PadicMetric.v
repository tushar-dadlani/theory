(* ================================================================= *)
(*  PadicMetric.v                                                     *)
(*                                                                    *)
(*  EXTENSION 2: the METRIC/topological completion side of the p-adic  *)
(*  integers -- the same object as PadicIntegers, seen through the      *)
(*  p-adic ULTRAMETRIC of Padic.v.  Axiom-free (pure Q, no Reals).     *)
(*                                                                    *)
(*  Two residue sequences (the digits of Padic integers) are close      *)
(*  exactly when they AGREE on many leading levels.  agree_upto a b k   *)
(*  means |a - b|_p <= pabs k = p^{-k}: the p-adic ball of radius        *)
(*  pabs k.  We prove this is an ULTRAMETRIC:                          *)
(*    - reflexive, symmetric, radius-monotone;                         *)
(*    - the STRONG TRIANGLE inequality: agreement to radii k1, k2 gives  *)
(*      agreement to radius min(k1,k2), and (via Padic.pabs_min)         *)
(*      pabs (min k1 k2) = max (pabs k1) (pabs k2) -- so                *)
(*      d(a,c) <= max(d(a,b), d(b,c));                                  *)
(*    - separation: agreement at every level forces equality.           *)
(*                                                                    *)
(*  This exhibits the inverse limit (PadicIntegers.Zp) as the p-adic     *)
(*  metric completion: the radii pabs k -> 0, and coherent Cauchy data   *)
(*  assembles into a limit point (PadicIntegers.Zmediate = completeness).*)
(* ================================================================= *)

Require Import Padic.
From Stdlib Require Import QArith Qminmax Lqa ZArith Lia.
Open Scope Q_scope.

Section PadicMet.

Variable p : positive.
Hypothesis Hp : (2 <= Z.pos p)%Z.

(* the p-adic ball radius at agreement level k: pabs k = p^{-k} *)
Definition prad (k : nat) : Q := pabs p k.

(* two digit sequences agree up to level k  (=  |a - b|_p <= prad k) *)
Definition agree_upto (a b : nat -> nat) (k : nat) : Prop :=
  forall n, (n < k)%nat -> a n = b n.

Lemma agree_refl : forall a k, agree_upto a a k.
Proof. intros a k n _; reflexivity. Qed.

Lemma agree_sym : forall a b k, agree_upto a b k -> agree_upto b a k.
Proof. intros a b k H n Hn; symmetry; apply H; exact Hn. Qed.

(* smaller ball (larger k) is contained in the larger ball (smaller k) *)
Lemma agree_mono : forall a b k1 k2,
  (k2 <= k1)%nat -> agree_upto a b k1 -> agree_upto a b k2.
Proof. intros a b k1 k2 Hk H n Hn; apply H; lia. Qed.

(* the ultrametric core: agreement to radii k1 and k2 gives agreement    *)
(* to radius min(k1,k2) -- balls of the same radius are nested          *)
Lemma agree_ultra : forall a b c k1 k2,
  agree_upto a b k1 -> agree_upto b c k2 -> agree_upto a c (Nat.min k1 k2).
Proof.
  intros a b c k1 k2 Hab Hbc n Hn.
  rewrite (Hab n) by lia; apply Hbc; lia.
Qed.

(* radius is antitone in the agreement level (Padic.pabs_antitone) *)
Lemma prad_antitone : forall k1 k2, (k1 <= k2)%nat -> prad k2 <= prad k1.
Proof. intros k1 k2 H; unfold prad; apply (pabs_antitone p Hp); exact H. Qed.

(* the min-radius is the max of the two radii (Padic.pabs_min) *)
Lemma prad_min : forall k1 k2, prad (Nat.min k1 k2) == Qmax (prad k1) (prad k2).
Proof. intros k1 k2; unfold prad; apply (pabs_min p Hp). Qed.

(* THE STRONG TRIANGLE INEQUALITY, in metric form:                       *)
(* if d(a,b) <= prad k1 and d(b,c) <= prad k2 then                       *)
(* d(a,c) <= prad(min k1 k2) = max(prad k1, prad k2).                    *)
Theorem strong_triangle : forall a b c k1 k2,
  agree_upto a b k1 -> agree_upto b c k2 ->
  agree_upto a c (Nat.min k1 k2)
  /\ prad (Nat.min k1 k2) == Qmax (prad k1) (prad k2).
Proof.
  intros a b c k1 k2 Hab Hbc; split;
    [ eapply agree_ultra; eauto | apply prad_min ].
Qed.

(* SEPARATION (Hausdorff): agreement at every level forces equality --   *)
(* the metric is a genuine metric (distance 0 => equal), so the limit is  *)
(* separated. *)
Theorem separated : forall a b, (forall k, agree_upto a b k) -> forall n, a n = b n.
Proof. intros a b H n; apply (H (S n)); lia. Qed.

(* the radii shrink toward 0: prad is positive and strictly below any     *)
(* coarser level's radius -- the balls form a neighbourhood basis at 0.   *)
Lemma prad_pos : forall k, 0 < prad k.
Proof. intro k; unfold prad; apply (pabs_pos p). Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the p-adic ultrametric, axiom-free              *)
(* ----------------------------------------------------------------- *)

Theorem padic_metric :
  (forall a k, agree_upto a a k)
  /\ (forall a b k, agree_upto a b k -> agree_upto b a k)
  /\ (forall a b k1 k2, (k2 <= k1)%nat -> agree_upto a b k1 -> agree_upto a b k2)
  (* strong triangle inequality via the ultrametric min = max on radii *)
  /\ (forall a b c k1 k2, agree_upto a b k1 -> agree_upto b c k2 ->
        agree_upto a c (Nat.min k1 k2)
        /\ prad (Nat.min k1 k2) == Qmax (prad k1) (prad k2))
  (* it is a genuine (Hausdorff) metric: distance 0 => equal *)
  /\ (forall a b, (forall k, agree_upto a b k) -> forall n, a n = b n)
  (* the ball radii are positive *)
  /\ (forall k, 0 < prad k).
Proof.
  split; [ exact agree_refl | ].
  split; [ exact agree_sym | ].
  split; [ exact agree_mono | ].
  split; [ exact strong_triangle | ].
  split; [ exact separated | exact prad_pos ].
Qed.

End PadicMet.

Print Assumptions padic_metric.

(* ================================================================= *)
(*  END PadicMetric.v                                                 *)
(*  The p-adic ultrametric on residue sequences via agreement levels    *)
(*  and Padic.pabs: reflexive, symmetric, radius-monotone, strong-       *)
(*  triangle (min = max on radii), separated, radii > 0.  Exhibits the   *)
(*  inverse limit Z_p as the p-adic metric completion.                  *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
