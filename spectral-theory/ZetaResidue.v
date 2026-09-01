(* ================================================================= *)
(*  ZetaResidue.v  --  the complex residue of zeta at s = 1.          *)
(*                                                                    *)
(*      lim_{s->1} (s-1) * zetaC s = 1                                *)
(*                                                                    *)
(*  docs/route_b_C4_newman_plan.md lists this as blocker "C0", on the *)
(*  grounds that "zetaC has no Laurent/pole structure at 1".  It does: *)
(*  the pole is literally the first summand of CZeta.zetaC, and the    *)
(*  regular part is uniformly bounded near s = 1 by the Euler-         *)
(*  Maclaurin tail estimate ZetaEM.htermC_tail evaluated at M = 0.     *)
(*  No new analytic infrastructure is needed for the VALUE half of C0. *)
(*                                                                    *)
(*  UPDATE: the remaining half of C0 -- Bfn HOLOMORPHIC at 1, not      *)
(*  merely convergent -- is NOT open either.  CZetaRegular6.BfnT_holo  *)
(*  already gives it (BfnT is total, = (s-1)*zF off 1, = 1 at 1, and    *)
(*  holomorphic on all of Re s > 0).  ZetaPoleCancel2.v does the        *)
(*  rewiring onto BfnT and closes C0.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv CSeries CZeta ZetaTrap ZetaEM.
Open Scope R_scope.

Lemma Rpower_base1 : forall y, Rpower 1 y = 1.
Proof. intro y. unfold Rpower. rewrite ln_1, Rmult_0_r. apply exp_0. Qed.

(* ----------------------------------------------------------------- *)
(*  The regular part is bounded by 2*Kh, with no series manipulation:  *)
(*  the M = 0 tail bound already controls everything past the first    *)
(*  term, and the first term obeys the same bound.                     *)
(* ----------------------------------------------------------------- *)

Lemma Cmod_htermC_0 : forall s, 0 <= Re s -> Cminus C1 s <> C0 ->
  Cmod (htermC s 0) <= Kh s.
Proof.
  intros s Hs Hs1.
  pose proof (Cmod_htermC_bound s 0%nat Hs Hs1) as Hb.
  replace (INR (S 0)) with 1 in Hb by (simpl; ring).
  rewrite Rpower_base1 in Hb.
  unfold Kh. lra.
Qed.

Lemma Hsum_bound : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cmod (Hsum s H0 H1) <= 2 * Kh s.
Proof.
  intros s H0 H1.
  pose proof (htermC_tail s H0 H1 0%nat) as Ht.
  cbn [Cpsum] in Ht.
  replace (INR (S 0)) with 1 in Ht by (simpl; ring).
  rewrite Rpower_base1 in Ht.
  pose proof (Cmod_htermC_0 s (Rlt_le _ _ H0) H1) as Hh.
  replace (Hsum s H0 H1)
    with (Cadd (Cminus (Hsum s H0 H1) (htermC s 0)) (htermC s 0)) by ring.
  eapply Rle_trans; [ apply Cmod_triangle | lra ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Near s = 1 the majorant constant Kh is small.                      *)
(* ----------------------------------------------------------------- *)

Lemma Kh_near_one : forall s, Cmod (Cminus s C1) <= / 2 -> Kh s <= 5 / 8.
Proof.
  intros s Hd.
  assert (Hs : Cmod s <= 3 / 2).
  { replace s with (Cadd (Cminus s C1) C1) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_C1. lra. }
  assert (H2 : RtoC 2 = Cadd C1 C1).
  { change C1 with (RtoC 1). rewrite <- RtoC_add. f_equal; try ring. }
  assert (Hs1 : Cmod (Cadd s C1) <= 5 / 2).
  { replace (Cadd s C1) with (Cadd (Cminus s C1) (RtoC 2))
      by (rewrite H2; ring).
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_RtoC, Rabs_right by lra. lra. }
  pose proof (Cmod_nonneg s). pose proof (Cmod_nonneg (Cadd s C1)).
  unfold Kh. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The residue, quantitatively.                                      *)
(* ----------------------------------------------------------------- *)

Theorem zeta_residue_bound : forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
  Cmod (Cminus s C1) <= / 2 ->
  Cmod (Cminus (Cmul (Cminus s C1) (zetaC s H0 H1)) C1)
  <= 2 * Cmod (Cminus s C1).
Proof.
  intros s H0 H1 Hd.
  assert (Hne : Cminus s C1 <> C0).
  { intro Hc. apply H1.
    replace (Cminus C1 s) with (Copp (Cminus s C1)) by ring.
    rewrite Hc. ring. }
  (* peel the pole *)
  assert (Hsplit : Cminus (Cmul (Cminus s C1) (zetaC s H0 H1)) C1
                 = Cmul (Cminus s C1) (Cadd (RtoC (/ 2)) (Hsum s H0 H1))).
  { rewrite (zetaC_trapezoid s H0 H1). field. exact Hne. }
  rewrite Hsplit, Cmod_mul.
  assert (Hreg : Cmod (Cadd (RtoC (/ 2)) (Hsum s H0 H1)) <= 2).
  { eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_RtoC, Rabs_right by lra.
    pose proof (Hsum_bound s H0 H1). pose proof (Kh_near_one s Hd). lra. }
  pose proof (Cmod_nonneg (Cminus s C1)).
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  The residue, as a limit.  This is the statement route B wants:     *)
(*  (s-1)*zeta(s) -> 1, i.e. Bfn extends to 1 with value 1 <> 0.       *)
(* ----------------------------------------------------------------- *)

Theorem zeta_residue_one : forall eps, 0 < eps ->
  exists del, 0 < del /\
    forall s (H0 : 0 < Re s) (H1 : Cminus C1 s <> C0),
      Cmod (Cminus s C1) < del ->
      Cmod (Cminus (Cmul (Cminus s C1) (zetaC s H0 H1)) C1) < eps.
Proof.
  intros eps He. exists (Rmin (/ 2) (eps / 2)).
  split; [ apply Rmin_glb_lt; lra | ].
  intros s H0 H1 Hd.
  assert (Hd2 : Cmod (Cminus s C1) <= / 2).
  { eapply Rle_trans; [ apply Rlt_le, Hd | apply Rmin_l ]. }
  assert (Hd3 : Cmod (Cminus s C1) < eps / 2).
  { eapply Rlt_le_trans; [ exact Hd | apply Rmin_r ]. }
  pose proof (zeta_residue_bound s H0 H1 Hd2). lra.
Qed.

Print Assumptions zeta_residue_one.
