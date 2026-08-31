(* ================================================================= *)
(*  ZSign.v  --  the sign of the Hardy Z function, from theta and zeta.*)
(*                                                                    *)
(*  GammaArg.Zfun_polar :                                             *)
(*      Z(t) = cos(theta t) Re zeta - sin(theta t) Im zeta,           *)
(*  XirSignZ.xir_neg_iff_Z_pos :  xir t < 0  <->  0 < Z(t).            *)
(*                                                                    *)
(*  Both factors are now certified: theta by ThetaEnclose and zeta by  *)
(*  ZetaEnclose.  Combining them decides the sign of xir WITHOUT       *)
(*  computing the exponentially small |Gamma| -- which is the whole    *)
(*  point of the Stage 2 factorisation.                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith.
Require Import ComplexField Cmodulus CZeta ZetaFn CoherenceSingularity
        IntervalArith IntervalArithFun IntervalCos IntervalAtan
        IntervalTrig CertifiedPi XirSignZ GammaArg ZetaEnclose.
Open Scope R_scope.

Definition IZ (pc mc nc : nat) (Th Zr Zi : Itv) : option Itv :=
  match Icos_itvc pc mc nc Th, Isin_itvc pc mc nc Th with
  | Some Cv, Some Sv => Some (Isub (Imul Cv Zr) (Imul Sv Zi))
  | _, _ => None
  end.

Theorem IZ_sound : forall pc mc nc Th Zr Zi i t,
  0 <= t ->
  Icontains Th (theta t) ->
  Icontains Zr (Re (zF (crit t))) ->
  Icontains Zi (Im (zF (crit t))) ->
  IZ pc mc nc Th Zr Zi = Some i ->
  Icontains i (Zfun t).
Proof.
  intros pc mc nc Th Zr Zi i t Ht HTh HZr HZi H.
  unfold IZ in H.
  destruct (Icos_itvc pc mc nc Th) eqn:HC; [ | discriminate ].
  destruct (Isin_itvc pc mc nc Th) eqn:HS; [ | discriminate ].
  injection H as <-.
  rewrite (Zfun_polar t Ht).
  apply Isub_sound; apply Imul_sound; try assumption.
  - apply (Icos_itvc_sound pc mc nc Th); assumption.
  - apply (Isin_itvc_sound pc mc nc Th); assumption.
Qed.

(* ---- the sign test ---- *)

Theorem xir_neg_of_IZ : forall pc mc nc Th Zr Zi i t,
  0 <= t ->
  Icontains Th (theta t) ->
  Icontains Zr (Re (zF (crit t))) ->
  Icontains Zi (Im (zF (crit t))) ->
  IZ pc mc nc Th Zr Zi = Some i ->
  0 < Q2R (ilo i) ->
  xir t < 0.
Proof.
  intros pc mc nc Th Zr Zi i t Ht HTh HZr HZi H Hpos.
  apply (proj2 (xir_neg_iff_Z_pos t)).
  destruct (IZ_sound pc mc nc Th Zr Zi i t Ht HTh HZr HZi H) as [Hlo _].
  lra.
Qed.

Theorem xir_pos_of_IZ : forall pc mc nc Th Zr Zi i t,
  0 <= t ->
  Icontains Th (theta t) ->
  Icontains Zr (Re (zF (crit t))) ->
  Icontains Zi (Im (zF (crit t))) ->
  IZ pc mc nc Th Zr Zi = Some i ->
  Q2R (ihi i) < 0 ->
  0 < xir t.
Proof.
  intros pc mc nc Th Zr Zi i t Ht HTh HZr HZi H Hneg.
  apply (proj2 (xir_pos_iff_Z_neg t)).
  destruct (IZ_sound pc mc nc Th Zr Zi i t Ht HTh HZr HZi H) as [_ Hhi].
  lra.
Qed.
