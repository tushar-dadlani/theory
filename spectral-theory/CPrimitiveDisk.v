(* ================================================================= *)
(*  CPrimitiveDisk.v  —  Hadamard keystone, brick A:                    *)
(*  a function holomorphic on a disk has a holomorphic primitive.       *)
(*                                                                    *)
(*    primitive_on_disk : F holomorphic on { |z| < Rr }  ==>           *)
(*      exists G, forall z in the disk, is_Cderiv G z (F z).           *)
(*                                                                    *)
(*  This is the missing tool for the HOLOMORPHIC COMPLEX LOGARITHM      *)
(*  (brick B): applying it to  g = F'/F  (holomorphic where F<>0) gives *)
(*  a primitive of F'/F, i.e. Log F up to a constant -- which unblocks  *)
(*  the zero-free mean value property (brick 3's other half) and the    *)
(*  Hadamard uniqueness step (brick 6).                                 *)
(*                                                                    *)
(*  The heavy lifting is already in the repo: CGoursatExcept.PrimE_deriv *)
(*  builds the segment-integral primitive  PrimE = seg_int F z0  on any *)
(*  convex open set (Goursat on triangles => path-independence => FTC). *)
(*  This file instantiates it on a disk, discharging the (removable-    *)
(*  singularity) exception hypotheses trivially since F is FULLY        *)
(*  holomorphic there (holomorphic => continuous => locally bounded,    *)
(*  via CHoloCalculus.is_Cderiv_cont).                                  *)
(*                                                                    *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CSegInt CPathIntegral CGoursatExcept
        CHoloCalculus CPrimConv Holomorphic.
Open Scope R_scope.

(* the open disk of radius Rr centered at the origin *)
Definition disk (Rr : R) (z : C) : Prop := Cmod z < Rr.

Lemma disk_convex : forall Rr, Convex (disk Rr).
Proof.
  intros Rr a b Ha Hb s [Hs0 Hs1]. unfold disk in *.
  replace (seg a b s) with (Cadd (Cmul (Cminus C1 (RtoC s)) a) (Cmul (RtoC s) b))
    by (unfold seg; ring).
  assert (Hcs : Cminus C1 (RtoC s) = RtoC (1 - s)) by (apply Ceq; simpl; lra).
  rewrite Hcs.
  eapply Rle_lt_trans; [ apply Cmod_triangle | ].
  rewrite !Cmod_mul, !Cmod_RtoC.
  rewrite (Rabs_right (1 - s)) by lra. rewrite (Rabs_right s) by lra.
  pose proof (Cmod_nonneg a) as Hna. pose proof (Cmod_nonneg b) as Hnb.
  destruct (Rlt_le_dec s 1) as [Hslt | Hsge].
  - apply Rle_lt_trans with ((1 - s) * Cmod a + s * Rr).
    + apply Rplus_le_compat_l. apply Rmult_le_compat_l; lra.
    + apply Rlt_le_trans with ((1 - s) * Rr + s * Rr).
      * apply Rplus_lt_compat_r. apply Rmult_lt_compat_l; lra.
      * lra.
  - assert (s = 1) by lra. subst s.
    replace ((1 - 1) * Cmod a + 1 * Cmod b) with (Cmod b) by ring. exact Hb.
Qed.

Lemma disk_open : forall Rr, Open (disk Rr).
Proof.
  intros Rr z Hz. unfold disk in *. exists (Rr - Cmod z). split; [ lra | ].
  intros w Hw.
  assert (Cmod w <= Cmod z + Cmod (Cminus w z)).
  { pose proof (Cmod_triangle z (Cminus w z)) as HT.
    replace (Cadd z (Cminus w z)) with w in HT by ring. exact HT. }
  lra.
Qed.

(* holomorphic => continuous, in the w-form (from is_Cderiv_cont) *)
Lemma Cderiv_cont_w : forall F z d, is_Cderiv F z d ->
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps.
Proof.
  intros F z d Hd eps Heps.
  destruct (is_Cderiv_cont F z d Hd eps Heps) as [del [Hdel Hb]].
  exists del. split; [ exact Hdel | ]. intros w Hw.
  specialize (Hb (Cminus w z) Hw).
  replace (Cadd z (Cminus w z)) with w in Hb by ring. exact Hb.
Qed.

(* THE brick: primitive existence on a disk *)
Theorem primitive_on_disk : forall (Rr : R) (F : C -> C) (HF : CcontC F),
  0 < Rr ->
  (forall z, disk Rr z -> exists d, is_Cderiv F z d) ->
  exists G : C -> C, forall z, disk Rr z -> is_Cderiv G z (F z).
Proof.
  intros Rr F HF HR Hhol.
  assert (HCmodC0 : Cmod C0 = 0) by (apply (proj2 (Cmod0 C0)); reflexivity).
  assert (HdiskC0 : disk Rr C0) by (unfold disk; rewrite HCmodC0; exact HR).
  exists (PrimE F HF C0). intros z Hz.
  apply (PrimE_deriv (disk Rr) (disk_convex Rr) (disk_open Rr) F HF C0 HdiskC0).
  - (* HFhol : holomorphic on U\{p} -- drop the exception *)
    intros z' Hz' _. apply Hhol; exact Hz'.
  - (* HFbd : F locally bounded near p = C0 (from continuity at C0) *)
    destruct (Hhol C0 HdiskC0) as [d0 Hd0].
    destruct (Cderiv_cont_w F C0 d0 Hd0 1 Rlt_0_1) as [eta [Heta Hb0]].
    exists (Cmod (F C0) + 1), eta. split; [ exact Heta | ]. intros w Hw.
    apply Rle_trans with (Cmod (F C0) + Cmod (Cminus (F w) (F C0))).
    + pose proof (Cmod_triangle (F C0) (Cminus (F w) (F C0))) as HT.
      replace (Cadd (F C0) (Cminus (F w) (F C0))) with (F w) in HT by ring. exact HT.
    + specialize (Hb0 w Hw). lra.
  - (* HFcont : F continuous on U (from holomorphy) *)
    intros z' Hz' eps Heps. destruct (Hhol z' Hz') as [d' Hd'].
    exact (Cderiv_cont_w F z' d' Hd' eps Heps).
  - (* HUz0 *) exact HdiskC0.
  - (* U z *) exact Hz.
Qed.

Print Assumptions primitive_on_disk.
