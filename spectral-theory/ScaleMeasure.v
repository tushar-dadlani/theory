(* ================================================================= *)
(*  ScaleMeasure.v  —  RUNG 3b of the Erdos-Selberg limsup layer.       *)
(*                                                                    *)
(*  The missing primitive: a weighted "measure of the set of scales     *)
(*  where the normalised remainder Vrem is large".  For a weight w and  *)
(*  a range [a, a+k):                                                   *)
(*                                                                    *)
(*    smeas c w a k  :=  Sum_{n in [a,a+k), Vrem n >= c}  w n.          *)
(*                                                                    *)
(*  (taking w n = /INR n gives the logarithmic measure the cancellation *)
(*  argument uses.)  We prove the algebra a density layer needs:        *)
(*    smeas_nonneg           (w>=0 => measure >= 0)                     *)
(*    smeas_le_wsum          (measure <= total weight)                  *)
(*    smeas_thresh_antitone  (higher threshold => smaller measure)      *)
(*    smeas_markov  : c * smeas c w a k <= Sum w n * Vrem n             *)
(*         -- the Markov/Chebyshev bridge: the measure of the extremal   *)
(*            set is at most (weighted average of Vrem) / c.            *)
(*                                                                    *)
(*  and the genuinely-new spike-driven input (from RemSpike):           *)
(*    spike_block_pos : a positive excursion of height a at n0 forces    *)
(*         Vrem n >= a/2 across the whole block [n0, 2(a+1)/(a+2)*n0].   *)
(*         -- "a large value of |R| is not a point, it fills an interval".*)
(*                                                                    *)
(*  This is the layer with no prior analog in the repo (which had only   *)
(*  plain counting).  Axiom-clean.                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound VonMangoldtGlobal RealMobius
        MobiusOverD MuLog SelbergEndgame RemSpike SelbergAverage.
Open Scope R_scope.

(* Real indicator of {Vrem n >= c}. *)
Definition ind_ge (c : R) (n : nat) : R := if Rle_dec c (Vrem n) then 1 else 0.

(* Weighted measure of {n in [a,a+k) : Vrem n >= c}. *)
Definition smeas (c : R) (w : nat -> R) (a k : nat) : R :=
  Rls (seq a k) (fun n => w n * ind_ge c n).

(* ----------------------------------------------------------------- *)
(*  Basic algebra.                                                    *)
(* ----------------------------------------------------------------- *)

Lemma smeas_nonneg : forall c w a k,
  (forall n, In n (seq a k) -> 0 <= w n) -> 0 <= smeas c w a k.
Proof.
  intros c w a k Hw; unfold smeas.
  replace 0 with (Rls (seq a k) (fun _ => 0)) by (apply Rls_zero).
  apply Rls_le; intros n Hn; unfold ind_ge.
  destruct (Rle_dec c (Vrem n)).
  - rewrite Rmult_1_r; apply Hw; exact Hn.
  - rewrite Rmult_0_r; apply Rle_refl.
Qed.

Lemma smeas_le_wsum : forall c w a k,
  (forall n, In n (seq a k) -> 0 <= w n) -> smeas c w a k <= Rls (seq a k) w.
Proof.
  intros c w a k Hw; unfold smeas; apply Rls_le; intros n Hn; unfold ind_ge.
  destruct (Rle_dec c (Vrem n)).
  - rewrite Rmult_1_r; apply Rle_refl.
  - rewrite Rmult_0_r; apply Hw; exact Hn.
Qed.

Lemma smeas_thresh_antitone : forall c1 c2 w a k,
  c1 <= c2 -> (forall n, In n (seq a k) -> 0 <= w n) ->
  smeas c2 w a k <= smeas c1 w a k.
Proof.
  intros c1 c2 w a k Hc Hw; unfold smeas; apply Rls_le; intros n Hn; unfold ind_ge.
  destruct (Rle_dec c2 (Vrem n)) as [H2 | H2];
    destruct (Rle_dec c1 (Vrem n)) as [H1 | H1].
  - apply Rle_refl.
  - exfalso; apply H1; lra.
  - rewrite Rmult_0_r, Rmult_1_r; apply Hw; exact Hn.
  - apply Rle_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  The Markov / Chebyshev bridge: measure <= average / c.            *)
(* ----------------------------------------------------------------- *)

Theorem smeas_markov : forall c w a k,
  (forall n, In n (seq a k) -> 0 <= w n) ->
  c * smeas c w a k <= Rls (seq a k) (fun n => w n * Vrem n).
Proof.
  intros c w a k Hw; unfold smeas; rewrite Rls_scal.
  apply Rls_le; intros n Hn; unfold ind_ge.
  destruct (Rle_dec c (Vrem n)) as [Hc | Hc].
  - replace (w n * 1) with (w n) by ring.
    rewrite (Rmult_comm c (w n)); apply Rmult_le_compat_l;
      [ apply Hw; exact Hn | exact Hc ].
  - replace (c * (w n * 0)) with 0 by ring.
    apply Rmult_le_pos; [ apply Hw; exact Hn | apply Vrem_nonneg ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The spike-block: a large value of |R| fills a whole interval.     *)
(* ----------------------------------------------------------------- *)

Theorem spike_block_pos : forall n0 n a,
  0 < a -> (1 <= n0)%nat -> a * INR n0 <= Rem n0 ->
  (n0 <= n)%nat -> (a + 2) * INR n <= 2 * (a + 1) * INR n0 ->
  a / 2 <= Vrem n.
Proof.
  intros n0 n a Ha Hn0 Hspike Hle Hblock.
  assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
  pose proof (pos_INR n0) as Hn0R.
  assert (H2 : Rem n0 - (INR n - INR n0) <= Rem n) by (apply Rem_mono_lb; exact Hle).
  assert (HRn : a / 2 * INR n <= Rem n) by nra.
  assert (HRnpos : 0 <= Rem n) by nra.
  unfold Vrem; rewrite (Rabs_pos_eq (Rem n)) by exact HRnpos.
  apply Rmult_le_reg_r with (INR n); [ exact HnR | ].
  replace (Rem n / INR n * INR n) with (Rem n) by (field; lra).
  exact HRn.
Qed.

(* The negative analog: a negative excursion of height a (< 1) at n0 forces
   Vrem m >= a/2 BACKWARD across [ (2-2a)/(2-a) * n0, n0 ] (Rem_mono_ub_back). *)
Theorem spike_block_neg : forall n0 m a,
  0 < a -> (1 <= m)%nat -> Rem n0 <= - a * INR n0 ->
  (m <= n0)%nat -> 2 * (1 - a) * INR n0 <= (2 - a) * INR m ->
  a / 2 <= Vrem m.
Proof.
  intros n0 m a Ha Hm Hspike Hle Hblock.
  assert (HmR : 0 < INR m) by (apply lt_0_INR; lia).
  pose proof (pos_INR n0) as Hn0R.
  assert (H2 : Rem m <= Rem n0 + (INR n0 - INR m)) by (apply Rem_mono_ub_back; exact Hle).
  assert (HRm : Rem m <= - (a / 2) * INR m) by nra.
  assert (HRmneg : Rem m <= 0) by nra.
  unfold Vrem; rewrite (Rabs_left1 (Rem m)) by exact HRmneg.
  apply Rmult_le_reg_r with (INR m); [ exact HmR | ].
  replace (- Rem m / INR m * INR m) with (- Rem m) by (field; lra).
  nra.
Qed.

Print Assumptions smeas_markov.
Print Assumptions spike_block_neg.

(* ================================================================= *)
(*  END ScaleMeasure.v  —  RUNG 3b: the scale-measure primitive.       *)
(* ================================================================= *)
