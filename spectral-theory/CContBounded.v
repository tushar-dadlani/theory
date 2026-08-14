(* ================================================================= *)
(*  CContBounded.v  (identity-theorem plan, FE chain brick 5 — base)    *)
(*                                                                    *)
(*  A path-continuous f : R -> C is bounded on any [a,b].  This is the   *)
(*  compactness input the scaled walk needs everywhere: it turns        *)
(*  "F holomorphic on {Re>0}" (hence continuous) into the circle        *)
(*  bounds (Hgb) that the Cauchy tower consumes.  Proof: stdlib's       *)
(*  continuity_ab_maj/min on Re.f and Im.f (Ccont = continuity of both) *)
(*  + Cmod c <= |Re c| + |Im c|.                                       *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CIntegral2.
Open Scope R_scope.

Lemma Cmod_le_ReIm : forall c, Cmod c <= Rabs (Re c) + Rabs (Im c).
Proof.
  intro c.
  assert (Hs : 0 <= Rabs (Re c) + Rabs (Im c))
    by (apply Rplus_le_le_0_compat; apply Rabs_pos).
  unfold Cmod.
  rewrite <- (sqrt_square (Rabs (Re c) + Rabs (Im c))) by exact Hs.
  apply sqrt_le_1_alt. unfold Cnorm2.
  pose proof (Rsqr_abs (Re c)) as Hr; pose proof (Rsqr_abs (Im c)) as Hi.
  unfold Rsqr in *.
  pose proof (Rabs_pos (Re c)); pose proof (Rabs_pos (Im c)).
  nra.
Qed.

Lemma abs_bound_between : forall x lo hi, lo <= x -> x <= hi ->
  Rabs x <= Rabs lo + Rabs hi.
Proof.
  intros x lo hi Hlo Hhi.
  pose proof (Rle_abs hi). pose proof (Rle_abs (- lo)). rewrite Rabs_Ropp in *.
  pose proof (Rabs_pos lo). pose proof (Rabs_pos hi).
  apply Rabs_le. split; lra.
Qed.

Theorem Ccont_bounded : forall (f : R -> C), Ccont f -> forall a b, a <= b ->
  exists M, forall u, a <= u <= b -> Cmod (f u) <= M.
Proof.
  intros f [HRe HIm] a b Hab.
  destruct (continuity_ab_maj (fun u => Re (f u)) a b Hab (fun c (_ : a <= c <= b) => HRe c)) as [xM [HxM _]].
  destruct (continuity_ab_min (fun u => Re (f u)) a b Hab (fun c (_ : a <= c <= b) => HRe c)) as [xm [Hxm _]].
  destruct (continuity_ab_maj (fun u => Im (f u)) a b Hab (fun c (_ : a <= c <= b) => HIm c)) as [yM [HyM _]].
  destruct (continuity_ab_min (fun u => Im (f u)) a b Hab (fun c (_ : a <= c <= b) => HIm c)) as [ym [Hym _]].
  exists (Rabs (Re (f xm)) + Rabs (Re (f xM))
          + (Rabs (Im (f ym)) + Rabs (Im (f yM)))).
  intros u Hu.
  eapply Rle_trans; [ apply Cmod_le_ReIm | ].
  assert (HR : Rabs (Re (f u)) <= Rabs (Re (f xm)) + Rabs (Re (f xM)))
    by (apply abs_bound_between; [ apply Hxm | apply HxM ]; exact Hu).
  assert (HI : Rabs (Im (f u)) <= Rabs (Im (f ym)) + Rabs (Im (f yM)))
    by (apply abs_bound_between; [ apply Hym | apply HyM ]; exact Hu).
  lra.
Qed.

Print Assumptions Ccont_bounded.
