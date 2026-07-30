(* ================================================================= *)
(*  FourierSincCore.v  —  the geometric core of the removable         *)
(*  singularity for the 2π-periodic C² localiser (Fourier F3).        *)
(*                                                                    *)
(*  The localiser g(y) = (f(y)−f(x))/sin((x−y)/2) for a 2π-periodic f *)
(*  factors as  g = h(y)·K(y),  where h(y) = ∫₀¹ f'(x+t(y−x)) dt is    *)
(*  globally smooth and the entire singularity sits in the UNIVERSAL  *)
(*  (f-independent) factor  K(y) = (y−x)/sin((x−y)/2) = −2·sinc(w),    *)
(*  w = (y−x)/2, where                                                *)
(*                                                                    *)
(*     sinc w := sin w / w   (extended by sinc 0 = 1).                *)
(*                                                                    *)
(*  This file resolves that universal removable singularity at the    *)
(*  C⁰ level:  the defining identity sinc(w)·w = sin w (all w), the    *)
(*  continuous extension across w = 0 (sinc 0 = 1, via sin′(0)=1),     *)
(*  and positivity 0 < sinc w on (−π,π) (so the reciprocal is         *)
(*  available).  These are exactly the reciprocal-ready facts the      *)
(*  localiser factor K needs on the period.                          *)
(*                                                                    *)
(*  Still ahead for the full C² result (each substantial): the C¹     *)
(*  upgrade of sinc (Taylor bounds sin_bound/cos_bound), the smooth    *)
(*  factor h (FTC / differentiation under the integral), and the      *)
(*  global antiperiodic C¹ assembly into a C1_fun.                    *)
(*                                                                    *)
(*  No new axioms (classical Reals only).                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Definition sinc (w : R) : R := if Req_dec_T w 0 then 1 else sin w / w.

Lemma sinc_0 : sinc 0 = 1.
Proof. unfold sinc; destruct (Req_dec_T 0 0) as [_ | H]; [ reflexivity | now elim H ]. Qed.

(* the defining identity, total (w = 0: 1·0 = 0 = sin 0) *)
Lemma sinc_id : forall w, sinc w * w = sin w.
Proof.
  intro w; unfold sinc; destruct (Req_dec_T w 0) as [-> | Hw];
    [ rewrite sin_0; ring | field; exact Hw ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Continuity, incl. across the removable point w = 0.              *)
(* ----------------------------------------------------------------- *)

(* congruence: continuity is a local property *)
Lemma continuity_pt_loceq : forall (f g : R -> R) x (d : posreal),
  (forall y, Rabs (y - x) < d -> f y = g y) -> continuity_pt g x -> continuity_pt f x.
Proof.
  intros f g x d Heq Hg.
  assert (Hfx : f x = g x)
    by (apply Heq; unfold Rminus; rewrite Rplus_opp_r, Rabs_R0; apply cond_pos).
  unfold continuity_pt, continue_in, limit1_in, limit_in in *.
  intros eps Heps; destruct (Hg eps Heps) as [alp [Halp Hy]].
  exists (Rmin alp d); split; [ apply Rmin_pos; [ exact Halp | apply cond_pos ] | ].
  intros y [Hdy Hdist]. simpl in Hdist |- *. unfold R_dist in Hdist |- *.
  assert (Hlt_alp : Rabs (y - x) < alp)
    by (eapply Rlt_le_trans; [ exact Hdist | apply Rmin_l ]).
  assert (Hlt_d : Rabs (y - x) < d)
    by (eapply Rlt_le_trans; [ exact Hdist | apply Rmin_r ]).
  rewrite (Heq y Hlt_d), Hfx.
  exact (Hy y (conj Hdy Hlt_alp)).
Qed.

Lemma sinc_cont_0 : continuity_pt sinc 0.
Proof.
  pose proof (derivable_pt_lim_sin 0) as Hd; rewrite cos_0 in Hd.
  unfold derivable_pt_lim in Hd.
  unfold continuity_pt, continue_in, limit1_in, limit_in; simpl.
  intros eps Heps; destruct (Hd eps Heps) as [delta Hdelta].
  exists (pos delta); split; [ apply cond_pos | ].
  intros y [[_ Hyne] Hdist]. unfold R_dist in Hdist |- *.
  assert (Hyne' : y <> 0) by (apply not_eq_sym; exact Hyne).
  assert (Hsy : sinc y = sin y / y)
    by (unfold sinc; destruct (Req_dec_T y 0) as [-> | _]; [ now elim Hyne' | reflexivity ]).
  rewrite Hsy, sinc_0.
  assert (Hyd : Rabs y < delta) by (rewrite Rminus_0_r in Hdist; exact Hdist).
  specialize (Hdelta y Hyne' Hyd).
  rewrite Rplus_0_l, sin_0, Rminus_0_r in Hdelta; exact Hdelta.
Qed.

Lemma sinc_cont : continuity sinc.
Proof.
  intro x; destruct (Req_dec_T x 0) as [-> | Hx]; [ apply sinc_cont_0 | ].
  apply (continuity_pt_loceq sinc (fun w => sin w / w) x
           (mkposreal (Rabs x) (Rabs_pos_lt x Hx))).
  - intros y Hy; unfold sinc; destruct (Req_dec_T y 0) as [-> | _]; [ | reflexivity ].
    exfalso; simpl in Hy; rewrite Rminus_0_l, Rabs_Ropp in Hy; lra.
  - apply (continuity_pt_div sin (fun w => w) x).
    + apply continuity_sin.
    + apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id.
    + exact Hx.
Qed.

(* ----------------------------------------------------------------- *)
(*  Positivity on the period:  0 < sinc w  for w ∈ (−π,π).           *)
(* ----------------------------------------------------------------- *)

Lemma sinc_pos : forall w, - PI < w < PI -> 0 < sinc w.
Proof.
  intros w [Hlo Hhi]; unfold sinc; destruct (Req_dec_T w 0) as [-> | Hw]; [ lra | ].
  destruct (Rlt_or_le 0 w) as [Hpos | Hnp].
  - apply Rdiv_lt_0_compat; [ apply sin_gt_0; lra | exact Hpos ].
  - assert (Hneg : w < 0) by (destruct Hnp as [H | H]; [ exact H | now elim Hw ]).
    assert (Hsnw : 0 < sin (- w)) by (apply sin_gt_0; lra).
    rewrite sin_neg in Hsnw.
    replace (sin w / w) with ((- sin w) / (- w)) by (field; exact Hw).
    apply Rdiv_lt_0_compat; lra.
Qed.

Print Assumptions sinc_id.
Print Assumptions sinc_cont.
Print Assumptions sinc_pos.

(* ================================================================= *)
(*  END FourierSincCore.v                                            *)
(*  The universal removable-singularity factor sinc = sin w / w is    *)
(*  continuously extended across w = 0 and positive on (−π,π), with    *)
(*  sinc(w)·w = sin w.  This is the f-independent geometric core of    *)
(*  the 2π-periodic C² localiser; the C¹ upgrade and the global        *)
(*  antiperiodic C¹ assembly remain.                                 *)
(* ================================================================= *)
