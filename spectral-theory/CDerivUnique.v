(* ================================================================= *)
(*  CDerivUnique.v  (identity-theorem plan, FE chain brick 5 — helper)  *)
(*                                                                    *)
(*  Uniqueness of the complex derivative: is_Cderiv F z d1 and         *)
(*  is_Cderiv F z d2 force d1 = d2.  Standard eps-delta: both give      *)
(*  |Delta - d_i h| <= eps|h|, so |(d1-d2)h| <= 2 eps |h|, hence        *)
(*  |d1-d2| <= 2 eps for all eps, so d1 = d2.  Needed to conclude       *)
(*  the tower level is 0 where the function is locally 0.              *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic.
Open Scope R_scope.

Theorem is_Cderiv_unique : forall F z d1 d2,
  is_Cderiv F z d1 -> is_Cderiv F z d2 -> d1 = d2.
Proof.
  intros F z d1 d2 H1 H2.
  assert (Hbound : forall eps, 0 < eps -> Cmod (Cminus d1 d2) <= 2 * eps).
  { intros eps Heps.
    destruct (H1 eps Heps) as [del1 [Hdel1 Hb1]].
    destruct (H2 eps Heps) as [del2 [Hdel2 Hb2]].
    set (del := Rmin del1 del2).
    assert (Hdl1 : del <= del1) by apply Rmin_l.
    assert (Hdl2 : del <= del2) by apply Rmin_r.
    assert (Hdelpos : 0 < del) by (apply Rmin_glb_lt; assumption).
    set (h := RtoC (del / 2)).
    assert (Hhmod : Cmod h = del / 2)
      by (unfold h; rewrite Cmod_RtoC, Rabs_right by lra; reflexivity).
    assert (Hhpos : 0 < Cmod h) by (rewrite Hhmod; lra).
    assert (Hh1 : Cmod h < del1) by (rewrite Hhmod; lra).
    assert (Hh2 : Cmod h < del2) by (rewrite Hhmod; lra).
    pose proof (Hb1 h Hh1) as B1.
    pose proof (Hb2 h Hh2) as B2.
    assert (Hdh : Cmod (Cmul (Cminus d1 d2) h) <= 2 * eps * Cmod h).
    { replace (Cmul (Cminus d1 d2) h)
        with (Cminus (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d2 h))
                     (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d1 h))) by ring.
      eapply Rle_trans.
      - replace (Cminus (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d2 h))
                        (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d1 h)))
          with (Cadd (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d2 h))
                     (Copp (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d1 h)))) by ring.
        apply Cmod_triangle.
      - rewrite Cmod_opp. lra. }
    rewrite Cmod_mul in Hdh.
    apply (Rmult_le_reg_r (Cmod h)); [ exact Hhpos | ].
    eapply Rle_trans; [ exact Hdh | ]. apply Req_le; ring. }
  assert (Hz : Cmod (Cminus d1 d2) <= 0).
  { apply Rnot_lt_le. intro Hpos.
    pose proof (Hbound (Cmod (Cminus d1 d2) / 4) ltac:(lra)) as Hb. lra. }
  pose proof (Cmod_nonneg (Cminus d1 d2)) as Hnn.
  assert (Heq0 : Cmod (Cminus d1 d2) = 0) by lra.
  apply Cmod0 in Heq0.
  replace d1 with (Cadd (Cminus d1 d2) d2) by ring.
  rewrite Heq0. ring.
Qed.

Print Assumptions is_Cderiv_unique.
