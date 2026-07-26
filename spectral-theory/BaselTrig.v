(* ================================================================= *)
(*  BaselTrig.v  —  the trigonometric squeeze for the Basel problem.  *)
(*                                                                    *)
(*  For x ∈ (0, π/2):   cot²x < 1/x² < 1 + cot²x,                     *)
(*  the two-sided bound that (with Σcot² = m(2m−1)/3) squeezes         *)
(*  Σ 1/k² to π²/6.  Built on stdlib `sin_lt_x` plus a new `x < tan x`*)
(*  (MVT on sin x − x·cos x).  Also a `Un_cv` sandwich lemma.          *)
(*                                                                    *)
(*  Over the classical `Reals` (quarantined).                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Local Open Scope R_scope.

Definition Rcot (x : R) : R := cos x / sin x.

(* ----------------------------------------------------------------- *)
(*  x < tan x on (0, π/2), via MVT on g x = sin x − x·cos x           *)
(* ----------------------------------------------------------------- *)
Definition gtan (x : R) : R := sin x - x * cos x.

Lemma gtan_deriv : forall x, derivable_pt_lim gtan x (x * sin x).
Proof.
  intro x; unfold gtan.
  replace (x * sin x) with (cos x - (1 * cos x + x * - sin x)) by ring.
  apply derivable_pt_lim_minus.
  - apply derivable_pt_lim_sin.
  - apply (derivable_pt_lim_mult id cos x 1 (- sin x)).
    + apply derivable_pt_lim_id.
    + apply derivable_pt_lim_cos.
Qed.

Lemma tan_lb : forall x, 0 < x -> x < PI / 2 -> x < tan x.
Proof.
  intros x Hx Hx2.
  assert (Hcos : 0 < cos x) by (apply cos_gt_0; lra).
  set (pr := fun y => exist (fun l => derivable_pt_lim gtan y l) (y * sin y) (gtan_deriv y)).
  assert (Hg : gtan 0 < gtan x).
  { apply (derive_increasing_interv 0 (PI / 2) gtan pr PI2_RGT_0).
    - intros t Ht; change (derive_pt gtan t (pr t)) with (t * sin t).
      apply Rmult_lt_0_compat; [ lra | apply sin_gt_0; lra ].
    - lra.
    - lra.
    - exact Hx. }
  unfold gtan in Hg; rewrite sin_0 in Hg.
  assert (Hxc : x * cos x < sin x) by (replace (0 * cos 0) with 0 in Hg by ring; lra).
  apply (Rmult_lt_reg_r (cos x)); [ exact Hcos | ].
  replace (tan x * cos x) with (sin x) by (unfold tan; field; lra).
  exact Hxc.
Qed.

(* ----------------------------------------------------------------- *)
(*  cot²x < 1/x² < 1 + cot²x  on (0, π/2)                             *)
(* ----------------------------------------------------------------- *)
Lemma cot_sq_bounds : forall x, 0 < x -> x < PI / 2 ->
  Rcot x ^ 2 < / x ^ 2 /\ / x ^ 2 < 1 + Rcot x ^ 2.
Proof.
  intros x Hx Hx2.
  assert (Hsin : 0 < sin x) by (apply sin_gt_0; lra).
  assert (Hcos : 0 < cos x) by (apply cos_gt_0; lra).
  assert (Hsx : sin x < x) by (apply sin_lt_x; lra).
  assert (Htx : x < tan x) by (apply tan_lb; lra).
  assert (Hxc : x * cos x < sin x).
  { replace (sin x) with (tan x * cos x) by (unfold tan; field; lra).
    apply Rmult_lt_compat_r; [ exact Hcos | exact Htx ]. }
  (* 1 + cot²x = 1/sin²x *)
  assert (Hone : 1 + Rcot x ^ 2 = / sin x ^ 2).
  { unfold Rcot; pose proof (sin2_cos2 x) as Hsc; unfold Rsqr in Hsc.
    replace (1 + (cos x / sin x) ^ 2) with ((sin x * sin x + cos x * cos x) / (sin x ^ 2))
      by (field; lra).
    replace (sin x * sin x + cos x * cos x) with 1 by lra.
    field; lra. }
  assert (Hxpos : 0 < x ^ 2) by nra.
  assert (Hspos : 0 < sin x ^ 2) by nra.
  split.
  - (* cot²x < 1/x² : x²·cos²x < sin²x *)
    unfold Rcot.
    apply (Rmult_lt_reg_r (x ^ 2 * sin x ^ 2)); [ nra | ].
    replace ((cos x / sin x) ^ 2 * (x ^ 2 * sin x ^ 2)) with (x ^ 2 * (cos x * cos x)) by (field; lra).
    replace (/ x ^ 2 * (x ^ 2 * sin x ^ 2)) with (sin x * sin x) by (field; lra).
    assert (Hxc0 : 0 <= x * cos x) by (apply Rmult_le_pos; lra).
    replace (x ^ 2 * (cos x * cos x)) with ((x * cos x) * (x * cos x)) by ring.
    nra.
  - (* 1/x² < 1 + cot²x = 1/sin²x : sin²x < x² *)
    rewrite Hone; apply Rinv_lt_contravar; nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  the sandwich theorem on Un_cv                                     *)
(* ----------------------------------------------------------------- *)
Lemma Un_cv_squeeze : forall (a b c : nat -> R) (L : R),
  Un_cv a L -> Un_cv c L -> (forall n, a n <= b n <= c n) -> Un_cv b L.
Proof.
  intros a b c L Ha Hc Hbnd eps Heps.
  destruct (Ha eps Heps) as [Na HNa]; destruct (Hc eps Heps) as [Nc HNc].
  exists (Nat.max Na Nc); intros n Hn.
  assert (HnA : (Na <= n)%nat) by lia; assert (HnC : (Nc <= n)%nat) by lia.
  specialize (HNa n HnA); specialize (HNc n HnC); specialize (Hbnd n).
  unfold R_dist in *; apply Rabs_def2 in HNa; apply Rabs_def2 in HNc.
  apply Rabs_def1; lra.
Qed.

(* ================================================================= *)
(*  END BaselTrig.v                                                  *)
(* ================================================================= *)
