(* ================================================================= *)
(*  XiPeelComplete.v  --  the per-radius complete peel of XiC,         *)
(*  UNCONDITIONAL.                                                    *)
(*                                                                    *)
(*    xi_peel_complete : forall R, 0 < R -> exists l G,               *)
(*      (forall z, XiC z = prodfac l z * G z)                         *)
(*      /\ disk_holo G (4R+2) /\ ptcont G                             *)
(*      /\ (forall w, In w l -> Cmod w < R)                           *)
(*      /\ (forall z, Cmod z < R -> G z <> C0)                        *)
(*                                                                    *)
(*    xi_zeros_caught : ... /\ (forall z, Cmod z < R -> XiC z = C0    *)
(*                                        -> In z l)                  *)
(*                                                                    *)
(*  CZeroFree.cofactor_zero_free already proves exactly this for any   *)
(*  F meeting four hypotheses, and ALL FOUR are already discharged for *)
(*  XiC in XiZeroCount.v (XiC_ptcont, XiC_disk_holo, XiC_circle_bound, *)
(*  Cmod_XiC_C0).  No file in the repo had ever applied it to XiC --   *)
(*  its only uses are inside JensenCountComplete and CPeelAtCentre,    *)
(*  where the peel list is immediately consumed by Jensen and thrown   *)
(*  away.  So the statement below is a wiring job, not new analysis.   *)
(*                                                                    *)
(*  WHY IT IS WORTH STATING.  ZeroEnum / ZeroEnumG are assumed in 13   *)
(*  files and proved in none.  Of ZeroEnum's four clauses the audit in *)
(*  docs/zero_enumeration_gap.md finds only clause 3 (every prefix is  *)
(*  a peel list) live, together with ZeroEnumG's clause 4 (the         *)
(*  cofactor is eventually zero-free on each disk).  This file proves  *)
(*  the PER-RADIUS form of both of those, unconditionally.  It is      *)
(*  therefore the honest measure of how much of the enumeration        *)
(*  hypothesis is already true: everything except the passage from     *)
(*  "for each radius, some list" to "one sequence, uniformly".         *)
(*                                                                    *)
(*  WHAT THIS IS NOT.  It is NOT XiPeel l.  XiPeel (XiZeroDensity.v:   *)
(*  109-113) demands ONE cofactor G that is holomorphic on EVERY disk  *)
(*  (forall R2, disk_holo G R2), i.e. entire; cofactor_zero_free gives *)
(*  disk_holo G R2 for the single R2 fixed in advance, and the list    *)
(*  itself moves with the radius.  Upgrading needs a DIRECTEDNESS      *)
(*  lemma -- that the peel lists at nested radii are nested -- and no  *)
(*  such lemma exists anywhere (no incl / Permutation / sublist result *)
(*  in CPeelBound.v, CZeroFree.v or CZeroListFactor.v).  That is the   *)
(*  gap, and this file does not close it.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Classical_Prop.
Require Import ComplexField Cmodulus Holomorphic CDeriv
        JensenMultiZero CZeroListFactor JensenCountComplete CZeroFree
        RiemannXiEntire XiZeroCount.
Import ListNotations.
Open Scope R_scope.

Lemma XiC_C0_ne0 : XiC C0 <> C0.
Proof.
  intro Hc. pose proof Cmod_XiC_C0 as H.
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in H. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The peel, at the radius cofactor_zero_free hands back (Rr / 4).    *)
(* ----------------------------------------------------------------- *)

Theorem xi_peel_complete_raw : forall Rr : R, 0 < Rr ->
  exists (l : list C) (G : C -> C),
    (forall z, XiC z = Cmul (prodfac l z) (G z))
    /\ disk_holo G (Rr + 2) /\ ptcont G
    /\ (forall w, In w l -> Cmod w < Rr / 4)
    /\ (forall z, Cmod z < Rr / 4 -> G z <> C0).
Proof.
  intros Rr HRr.
  destruct (cofactor_zero_free XiC (Rr + 2) Rr (XiM Rr) HRr ltac:(lra)
              XiC_C0_ne0 XiC_ptcont (XiC_disk_holo (Rr + 2))
              (XiC_circle_bound Rr HRr))
    as [l [G [Hid [Hhol [Hptc [Hsm Hne0]]]]]].
  exists l, G. repeat split; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  The same at a freely chosen radius R, by feeding Rr := 4 R.        *)
(* ----------------------------------------------------------------- *)

Theorem xi_peel_complete : forall R : R, 0 < R ->
  exists (l : list C) (G : C -> C),
    (forall z, XiC z = Cmul (prodfac l z) (G z))
    /\ disk_holo G (4 * R + 2) /\ ptcont G
    /\ (forall w, In w l -> Cmod w < R)
    /\ (forall z, Cmod z < R -> G z <> C0).
Proof.
  intros R HR.
  destruct (xi_peel_complete_raw (4 * R) ltac:(lra))
    as [l [G [Hid [Hhol [Hptc [Hsm Hne0]]]]]].
  exists l, G.
  assert (Hq : 4 * R / 4 = R) by field.
  rewrite Hq in Hsm, Hne0.
  repeat split; assumption.
Qed.

Print Assumptions xi_peel_complete.

(* ----------------------------------------------------------------- *)
(*  Completeness: the list really does catch every zero in the disk.   *)
(*  This is ZeroEnum's clause-4 content, per radius.                   *)
(* ----------------------------------------------------------------- *)

Theorem xi_zeros_caught : forall R : R, 0 < R ->
  exists (l : list C) (G : C -> C),
    (forall z, XiC z = Cmul (prodfac l z) (G z))
    /\ ptcont G
    /\ (forall w, In w l -> Cmod w < R)
    /\ (forall z, Cmod z < R -> G z <> C0)
    /\ (forall z, Cmod z < R -> XiC z = C0 -> In z l).
Proof.
  intros R HR.
  destruct (xi_peel_complete R HR) as [l [G [Hid [_ [Hptc [Hsm Hne0]]]]]].
  exists l, G. repeat split; try assumption.
  intros z Hz Hzero.
  apply prodfac_zero_inv.
  (* XiC z = prodfac l z * G z = 0 with G z <> 0 forces prodfac l z = 0 *)
  destruct (classic (prodfac l z = C0)) as [Hp | Hp]; [ exact Hp | ].
  exfalso. apply (Cmul_ne0 (prodfac l z) (G z) Hp (Hne0 z Hz)).
  rewrite <- (Hid z). exact Hzero.
Qed.

Print Assumptions xi_zeros_caught.

(* ================================================================= *)
(*  END XiPeelComplete.v                                              *)
(* ================================================================= *)
