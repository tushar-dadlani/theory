(* ================================================================= *)
(*  GaussImproper.v  —  Gaussian part-A stack, step 5c: the classical  *)
(*  improper-integral scaffold  ∫₀^∞ f = lim_{A→∞} ∫₀^A f (RiemannInt). *)
(*                                                                    *)
(*  (Distinct from ImproperIntegral.v, which builds ∫₀^∞ as a CReal     *)
(*  series for the primorial/CReal line.  Here we stay in stdlib's      *)
(*  classical RiemannInt, the setting of the Wallis/Gaussian squeeze.) *)
(*                                                                    *)
(*  stdlib RiemannInt has no improper integral.  For a NONNEGATIVE      *)
(*  integrand the partial integral A ↦ ∫₀^A f is nondecreasing, so its  *)
(*  limit at +∞ is well defined and is pinned down by ANY single        *)
(*  sequence Aₖ → ∞.  That transfers the √n-indexed Gaussian limit      *)
(*  (∫₀^√n → √π/2) to the honest A→∞ limit.                            *)
(*                                                                    *)
(*    monotone_seq_transfer : F nondecreasing on [0,∞), F(aₖ)→I along   *)
(*        one aₖ→∞  ⇒  F(bₖ)→I along EVERY bₖ→∞;                       *)
(*    pint      : the partial integral ∫₀^A f (f integrable everywhere);*)
(*    pint_mono : f ≥ 0 ⇒ ∫₀^A f nondecreasing in A;                   *)
(*    ImproperCv I : ∫₀^{bₖ} f → I for every bₖ→∞  (the ∫₀^∞ = I pred); *)
(*    improper_welldef : f ≥ 0 and ∫₀^{aₖ} f → I for one aₖ→∞           *)
(*        ⇒ ImproperCv I.                                             *)
(*                                                                    *)
(*  The mathematical heart (monotone_seq_transfer) is integral-free:    *)
(*  a bounded-monotone limit-at-infinity fact.  No new axioms          *)
(*  (classical Reals only).                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The mathematical core: a nondecreasing function's limit at +∞ is  *)
(*  pinned down by any one sequence tending to +∞.                    *)
(* ----------------------------------------------------------------- *)

Lemma monotone_seq_transfer : forall (F : R -> R) (I : R),
  (forall x y, 0 <= x -> x <= y -> F x <= F y) ->
  forall (a : nat -> R), (forall k, 0 <= a k) -> cv_infty a ->
    Un_cv (fun k => F (a k)) I ->
  forall (b : nat -> R), (forall k, 0 <= b k) -> cv_infty b ->
    Un_cv (fun k => F (b k)) I.
Proof.
  intros F I Hmono a Ha0 Hainf HaI b Hb0 Hbinf.
  (* Step 1: F is bounded above by I on [0,∞). *)
  assert (HFI : forall x, 0 <= x -> F x <= I).
  { intros x Hx.
    destruct (Rle_or_lt (F x) I) as [Hle | Hlt]; [ exact Hle | exfalso ].
    set (eps := F x - I).
    assert (Heps : eps > 0) by (unfold eps; lra).
    destruct (HaI eps Heps) as [K HK].
    destruct (Hainf x) as [Na HNa].
    set (k := max K Na).
    assert (H1 : F x <= F (a k))
      by (apply Hmono; [ exact Hx | pose proof (HNa k (Nat.le_max_r K Na)); lra ]).
    pose proof (HK k (Nat.le_max_l K Na)) as HKk; unfold R_dist in HKk.
    pose proof (Rabs_def2 _ _ HKk) as [Hlt2 _]; unfold eps in Hlt2; lra. }
  (* Step 2: pick x0 = a K with I - eps < F x0; then F is within eps for x >= x0. *)
  intros eps Heps.
  destruct (HaI eps Heps) as [K HK].
  pose proof (HK K (Nat.le_refl K)) as HKK; unfold R_dist in HKK.
  pose proof (Rabs_def2 _ _ HKK) as [_ Hlow].
  destruct (Hbinf (a K)) as [Nb HNb].
  exists Nb; intros n Hn.
  assert (Hup : F (b n) <= I) by (apply HFI; apply Hb0).
  assert (Hlo : I - eps < F (b n)).
  { apply Rlt_le_trans with (F (a K)); [ lra | ].
    apply Hmono; [ apply Ha0 | pose proof (HNb n Hn); lra ]. }
  unfold R_dist; apply Rabs_def1; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  Partial integral of an everywhere-integrable f.                  *)
(* ----------------------------------------------------------------- *)

Section PartialIntegral.

Variable f : R -> R.
Hypothesis Hint : forall a b, Riemann_integrable f a b.

Definition pint (A : R) : R := RiemannInt (Hint 0 A).

(* f ≥ 0 on [0,∞) ⇒ ∫₀^A f is nondecreasing. *)
Lemma pint_mono : (forall x, 0 <= x -> 0 <= f x) ->
  forall x y, 0 <= x -> x <= y -> pint x <= pint y.
Proof.
  intros Hpos x y Hx Hxy; unfold pint.
  (* ∫₀^x + ∫_x^y = ∫₀^y, and ∫_x^y ≥ 0 *)
  assert (Hxy0 : 0 <= RiemannInt (Hint x y)).
  { pose proof (RiemannInt_P15 (RiemannInt_P14 x y 0)) as Hz.
    apply Rle_trans with (RiemannInt (RiemannInt_P14 x y 0)).
    - rewrite Hz; ring_simplify; apply Rle_refl.
    - apply RiemannInt_P19; [ exact Hxy | intros t Ht; unfold fct_cte; apply Hpos; lra ]. }
  pose proof (RiemannInt_P26 (Hint 0 x) (Hint x y) (Hint 0 y)) as Hadd; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The improper integral ∫₀^∞ f = I, and its well-definedness.      *)
(* ----------------------------------------------------------------- *)

Definition ImproperCv (I : R) : Prop :=
  forall (b : nat -> R), (forall k, 0 <= b k) -> cv_infty b ->
    Un_cv (fun k => pint (b k)) I.

Theorem improper_welldef : (forall x, 0 <= x -> 0 <= f x) ->
  forall (a : nat -> R) (I : R),
    (forall k, 0 <= a k) -> cv_infty a -> Un_cv (fun k => pint (a k)) I ->
    ImproperCv I.
Proof.
  intros Hpos a I Ha0 Hainf HaI b Hb0 Hbinf.
  apply (monotone_seq_transfer pint I (pint_mono Hpos) a Ha0 Hainf HaI b Hb0 Hbinf).
Qed.

End PartialIntegral.

Print Assumptions monotone_seq_transfer.
Print Assumptions improper_welldef.

(* ================================================================= *)
(*  END GaussImproper.v                                              *)
(*  ∫₀^∞ f = lim_{A→∞} ∫₀^A f for f ≥ 0, well defined and pinned by any *)
(*  one Aₖ→∞ (monotone limit at infinity).  This is the scaffold that   *)
(*  will carry ∫₀^√n e^{−x²} → √π/2 to ∫₀^∞ e^{−x²} = √π/2, once the     *)
(*  squeeze ∫₀^√n(1−x²/n)ⁿ ≤ ∫₀^√n e^{−x²} is in place.               *)
(* ================================================================= *)
