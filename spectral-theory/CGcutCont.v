(* ================================================================= *)
(*  CGcutCont.v  —  disk-cofactor bridge: the cutoff of F'/F.           *)
(*                                                                    *)
(*  gcut g r1 rc z := g z . psi r1 rc (Cmod z)  is:                     *)
(*   * = g on the inner disk Cmod z < r1              (gcut_one)        *)
(*   * holomorphic on the inner disk                 (gcut_holo)       *)
(*   * pointwise Cmod-continuous EVERYWHERE           (gcut_cmod_cont)  *)
(*     even where g (= F'/F) has poles: outside the disk the cutoff     *)
(*     kills it (psi = 0), and inside it is a product of continuous.    *)
(*  This is the globally-continuous stand-in for F'/F that lets the     *)
(*  disk logarithm be built.  Axiom-clean.                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus Holomorphic CHoloCalculus CPrimitiveDisk CCutoff.
Open Scope R_scope.

Lemma Cmod_revtri : forall a b, Rabs (Cmod a - Cmod b) <= Cmod (Cminus a b).
Proof.
  intros a b; apply Rabs_le; split.
  - pose proof (Cmod_triangle (Cminus b a) a) as H.
    replace (Cadd (Cminus b a) a) with b in H by ring.
    replace (Cminus b a) with (Copp (Cminus a b)) in H by ring.
    rewrite Cmod_opp in H. lra.
  - pose proof (Cmod_triangle (Cminus a b) b) as H.
    replace (Cadd (Cminus a b) b) with a in H by ring. lra.
Qed.

Definition gcut (g : C -> C) (r1 rc : R) (z : C) : C :=
  Cmul (g z) (RtoC (psi r1 rc (Cmod z))).

Section Gcut.
Variable g : C -> C.
Variables r1 rc R2 : R.
Hypothesis Hr1 : 0 < r1.
Hypothesis Hr1c : r1 < rc.
Hypothesis HcR2 : rc < R2.
Hypothesis Hghol : forall z, Cmod z < R2 -> exists d, is_Cderiv g z d.

Lemma gcut_one : forall z, Cmod z < r1 -> gcut g r1 rc z = g z.
Proof.
  intros z Hz; unfold gcut.
  rewrite (psi_one r1 rc (Cmod z) Hr1c ltac:(lra)).
  replace (RtoC 1) with C1 by reflexivity. ring.
Qed.

Lemma gcut_holo : forall z, Cmod z < r1 -> exists d, is_Cderiv (gcut g r1 rc) z d.
Proof.
  intros z Hz. destruct (Hghol z ltac:(lra)) as [d Hd]. exists d.
  apply (is_Cderiv_ext_local (gcut g r1 rc) g z d (r1 - Cmod z) ltac:(lra)); [ | exact Hd ].
  intros w Hw. apply gcut_one.
  pose proof (Cmod_triangle (Cminus w z) z) as HT.
  replace (Cadd (Cminus w z) z) with w in HT by ring. lra.
Qed.

Lemma gcut_cmod_cont : forall z0 eps, 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z0) < del ->
    Cmod (Cminus (gcut g r1 rc w) (gcut g r1 rc z0)) < eps.
Proof.
  intros z0 eps Heps.
  destruct (Rlt_le_dec (Cmod z0) R2) as [Hin | Hout].
  - (* inside disk R2: product of continuous functions *)
    destruct (Hghol z0 Hin) as [dg Hdg].
    destruct (Cderiv_cont_w g z0 dg Hdg (eps / 2) ltac:(lra)) as [delg [Hdelg Hgc]].
    set (Mg := Cmod (g z0)).
    assert (HMg : 0 <= Mg) by (unfold Mg; apply Cmod_nonneg).
    set (del := Rmin delg (eps / 2 * (rc - r1) / (Mg + 1))).
    assert (Hdelpos : 0 < del).
    { unfold del; apply Rmin_pos; [ exact Hdelg | ].
      apply Rdiv_lt_0_compat; [ apply Rmult_lt_0_compat; lra | lra ]. }
    exists del; split; [ exact Hdelpos | ]; intros w Hw.
    assert (Hsplit : Cminus (gcut g r1 rc w) (gcut g r1 rc z0)
                   = Cadd (Cmul (Cminus (g w) (g z0)) (RtoC (psi r1 rc (Cmod w))))
                          (Cmul (g z0) (Cminus (RtoC (psi r1 rc (Cmod w)))
                                               (RtoC (psi r1 rc (Cmod z0))))))
      by (unfold gcut, Cmul, Cminus, Cadd, RtoC; apply Ceq; cbn; ring).
    assert (Hpw1 : Cmod (RtoC (psi r1 rc (Cmod w))) <= 1).
    { rewrite Cmod_RtoC, (Rabs_pos_eq (psi r1 rc (Cmod w))); apply psi_bounds. }
    assert (Hgwz : Cmod (Cminus (g w) (g z0)) < eps / 2)
      by (apply Hgc; eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ]).
    assert (Hppz : Cmod (Cminus (RtoC (psi r1 rc (Cmod w))) (RtoC (psi r1 rc (Cmod z0))))
                   <= / (rc - r1) * Cmod (Cminus w z0)).
    { replace (Cminus (RtoC (psi r1 rc (Cmod w))) (RtoC (psi r1 rc (Cmod z0))))
         with (RtoC (psi r1 rc (Cmod w) - psi r1 rc (Cmod z0)))
         by (unfold RtoC, Cminus; apply Ceq; cbn; ring).
      rewrite Cmod_RtoC.
      eapply Rle_trans; [ apply psi_lip; exact Hr1c | ].
      apply (Rmult_le_compat_l (/ (rc - r1)));
        [ left; apply Rinv_0_lt_compat; lra | apply Cmod_revtri ]. }
    assert (HwR : Cmod (Cminus w z0) < eps / 2 * (rc - r1) / (Mg + 1))
      by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
    assert (Hterm1 : Cmod (Cminus (g w) (g z0)) * Cmod (RtoC (psi r1 rc (Cmod w))) < eps / 2).
    { apply Rle_lt_trans with (Cmod (Cminus (g w) (g z0)) * 1);
        [ apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hpw1 ]
        | rewrite Rmult_1_r; exact Hgwz ]. }
    assert (Hterm2 : Cmod (g z0)
                     * Cmod (Cminus (RtoC (psi r1 rc (Cmod w))) (RtoC (psi r1 rc (Cmod z0))))
                     <= eps / 2).
    { apply Rle_trans with (Mg * (/ (rc - r1) * Cmod (Cminus w z0)));
        [ apply Rmult_le_compat_l; [ apply Cmod_nonneg | exact Hppz ] | ].
      rewrite <- Rmult_assoc.
      apply Rle_trans with (Mg * / (rc - r1) * (eps / 2 * (rc - r1) / (Mg + 1))).
      - apply (Rmult_le_compat_l (Mg * / (rc - r1)));
          [ apply Rmult_le_pos; [ exact HMg | left; apply Rinv_0_lt_compat; lra ]
          | apply Rlt_le; exact HwR ].
      - assert (Heq : Mg * / (rc - r1) * (eps / 2 * (rc - r1) / (Mg + 1))
                    = Mg * (eps / 2) / (Mg + 1)) by (field; lra).
        rewrite Heq. apply Rle_trans with ((Mg + 1) * (eps / 2) / (Mg + 1)).
        + unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; lra | ].
          apply Rmult_le_compat_r; lra.
        + apply Req_le; field; lra. }
    rewrite Hsplit.
    eapply Rle_lt_trans; [ apply Cmod_triangle | ]. rewrite !Cmod_mul.
    apply Rlt_le_trans with (eps / 2 + eps / 2);
      [ apply Rplus_lt_le_compat; [ exact Hterm1 | exact Hterm2 ] | lra ].
  - (* outside disk R2: gcut is 0 near z0 *)
    assert (Hzz : rc <= Cmod z0) by lra.
    exists (R2 - rc); split; [ lra | ]; intros w Hw.
    assert (Hcw : rc <= Cmod w).
    { pose proof (Cmod_revtri w z0) as HR.
      pose proof (Rle_abs (- (Cmod w - Cmod z0))) as Hb. rewrite Rabs_Ropp in Hb. lra. }
    assert (Hgw0 : gcut g r1 rc w = C0)
      by (unfold gcut; rewrite (psi_zero r1 rc (Cmod w) Hr1c Hcw);
          replace (RtoC 0) with C0 by reflexivity; ring).
    assert (Hgz0 : gcut g r1 rc z0 = C0)
      by (unfold gcut; rewrite (psi_zero r1 rc (Cmod z0) Hr1c Hzz);
          replace (RtoC 0) with C0 by reflexivity; ring).
    rewrite Hgw0, Hgz0. replace (Cminus C0 C0) with C0 by ring.
    rewrite (proj2 (Cmod0 C0) eq_refl); exact Heps.
Qed.

End Gcut.

Print Assumptions gcut_cmod_cont.
