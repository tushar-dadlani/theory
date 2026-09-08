(* ================================================================= *)
(*  CZeroFreeGen.v  --  CZeroFree with the peel radius parametrised.   *)
(*                                                                    *)
(*  cofactor_zero_free_gen : same maximal-peel argument as             *)
(*  CZeroFree.cofactor_zero_free, but the zeros are collected inside   *)
(*  alpha * Rr instead of Rr / 4, for any 0 < alpha < 1/2.             *)
(*                                                                    *)
(*  The side condition that made Rr/4 convenient still holds: the      *)
(*  peel disk must sit inside (R2 - 1)/2, and                          *)
(*      alpha * Rr < Rr / 2 < (R2 - 1) / 2                             *)
(*  whenever alpha < 1/2 and Rr + 1 < R2.  So nothing is lost.         *)
(*                                                                    *)
(*  bounded_has_max is reused verbatim from CZeroFree.                 *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Classical.
Require Import ComplexField Cmodulus Holomorphic CDeriv CPathIntegral
        JensenMultiZero CZeroFactorDisk CZeroListFactor
        CPeelBoundGen CZeroFree.
Open Scope R_scope.

Section ZeroFreeGen.

Variable alpha : R.
Hypothesis Halpha : 0 < alpha < / 2.

Definition PeelLenG (F : C -> C) (R2 Rr : R) (n : nat) : Prop :=
  exists (l : list C) (G : C -> C),
    (forall z, F z = Cmul (prodfac l z) (G z)) /\
    disk_holo G R2 /\ ptcont G /\
    (forall w, In w l -> Cmod w < alpha * Rr) /\
    length l = n.

Theorem cofactor_zero_free_gen : forall (F : C -> C) (R2 Rr M : R),
  0 < Rr -> Rr + 1 < R2 ->
  F C0 <> C0 ->
  ptcont F ->
  disk_holo F R2 ->
  (forall u, Cmod (F (arc Rr u)) <= M) ->
  exists (l : list C) (G : C -> C),
    (forall z, F z = Cmul (prodfac l z) (G z)) /\
    disk_holo G R2 /\ ptcont G /\
    (forall w, In w l -> Cmod w < alpha * Rr) /\
    (forall z, Cmod z < alpha * Rr -> G z <> C0).
Proof.
  intros F R2 Rr M HR HRR2 HF0 HFptc HFhol HM.
  destruct Halpha as [Ha0 Ha2].
  assert (HR2 : 1 < R2) by lra.
  (* the peel disk still sits inside both side conditions *)
  assert (Hsmall_peel : forall w : C, Cmod w < alpha * Rr -> Cmod w < (R2 - 1) / 2)
    by (intros w Hw; nra).
  assert (Hshrink : forall G : C -> C, disk_holo G R2 -> disk_holo G (Rr + 1))
    by (intros G HG z Hz; apply HG; lra).
  (* every peel list is short *)
  destruct (peel_length_bound_gen alpha Halpha F Rr M HR HF0 HM) as [N HN].
  assert (Hbd : forall n, PeelLenG F R2 Rr n -> (n <= N)%nat).
  { intros n [l [G [Hid [Hhol [Hptc [Hsm Hlen]]]]]].
    rewrite <- Hlen.
    apply (HN G l Hid Hptc (Hshrink G Hhol)).
    intros w Hw. left. apply Hsm; exact Hw. }
  (* the empty peel is available *)
  assert (H0 : PeelLenG F R2 Rr 0%nat).
  { exists nil, F. split; [ | split; [ | split; [ | split ] ] ].
    - intro z. cbn [prodfac]. ring.
    - exact HFhol.
    - exact HFptc.
    - intros w Hw; destruct Hw.
    - reflexivity. }
  (* so take a maximal one *)
  destruct (bounded_has_max (PeelLenG F R2 Rr) N H0 Hbd) as [m [Hm Hmax]].
  destruct Hm as [l [G [Hid [Hhol [Hptc [Hsm Hlen]]]]]].
  exists l, G. split; [ exact Hid | ]. split; [ exact Hhol | ].
  split; [ exact Hptc | ]. split; [ exact Hsm | ].
  (* a remaining zero could be peeled, lengthening the list *)
  intros w Hw HGw.
  destruct (DivBy_cons F G R2 l w HR2 (Hsmall_peel w Hw) Hid Hhol Hptc HGw)
    as [H [Hid' [Hhol' Hptc']]].
  assert (Hlonger : PeelLenG F R2 Rr (S m)).
  { exists (w :: l), H. split; [ exact Hid' | ]. split; [ exact Hhol' | ].
    split; [ exact Hptc' | ]. split.
    - intros w' [E | Hin]; [ subst w'; exact Hw | apply Hsm; exact Hin ].
    - cbn [length]. rewrite Hlen. reflexivity. }
  pose proof (Hmax (S m) Hlonger) as Hcontra. lia.
Qed.

End ZeroFreeGen.

Print Assumptions cofactor_zero_free_gen.

(* ================================================================= *)
(*  END CZeroFreeGen.v                                                *)
(* ================================================================= *)
