(* ================================================================= *)
(*  CTruncDisk.v  —  the open convex region on which the truncated       *)
(*  Cauchy formula lives:  U = {|z| < R} ∩ {Re z > −δ}  (an open disk    *)
(*  intersect an open half-plane).  Convex + Open, so it feeds           *)
(*  CTruncCauchy.trunc_cauchy / the exceptional-point primitive.         *)
(*  Chosen with R strictly larger than the contour radius and δ so that  *)
(*  the closed truncated contour sits strictly inside.                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus CPathIntegral CGoursat CPrimConv.
Open Scope R_scope.

(* |Re c| <= |c| : the real part never exceeds the modulus *)
Lemma Rabs_Re_le_Cmod : forall c, Rabs (Re c) <= Cmod c.
Proof.
  intro c. unfold Cmod, Cnorm2.
  rewrite <- (sqrt_Rsqr_abs (Re c)); unfold Rsqr.
  apply sqrt_le_1_alt.
  pose proof (Rle_0_sqr (Im c)); unfold Rsqr in *; lra.
Qed.

(* Cadd z (w − z) = w, and Cminus w C0 = w : simplifiers for Open *)
Lemma Cadd_diff : forall z w, Cadd z (Cminus w z) = w.
Proof. intros; apply Ceq; unfold Cadd, Cminus; cbn; ring. Qed.

Lemma Cminus_C0_r : forall c, Cminus c C0 = c.
Proof. intro c; apply Ceq; unfold Cminus, C0; cbn; ring. Qed.

Lemma Re_seg : forall a b s, Re (seg a b s) = Re a + s * (Re b - Re a).
Proof. intros; unfold seg, Cadd, Cmul, Cminus, RtoC; cbn; ring. Qed.

Lemma Re_Cminus : forall a b, Re (Cminus a b) = Re a - Re b.
Proof. intros; unfold Cminus; cbn; ring. Qed.

(* ---- the region ---- *)
Definition TruncDisk (R delta : R) (z : C) : Prop :=
  Cmod z < R /\ - delta < Re z.

Lemma TruncDisk_convex : forall R delta, Convex (TruncDisk R delta).
Proof.
  intros R delta a b [Ha_m Ha_r] [Hb_m Hb_r] s Hs. split.
  - (* modulus stays below R *)
    pose proof (seg_convex_bound a b C0 s Hs) as HB.
    rewrite !Cminus_C0_r in HB.
    eapply Rle_lt_trans; [ exact HB | apply Rmax_lub_lt; assumption ].
  - (* real part stays above −delta: a convex combination of positives *)
    rewrite Re_seg. destruct Hs as [Hs0 Hs1].
    destruct (Req_dec s 0) as [Hs_eq | Hs_ne].
    + subst s; lra.
    + assert (0 < s * (Re b + delta)) by (apply Rmult_lt_0_compat; lra).
      assert (0 <= (1 - s) * (Re a + delta)) by (apply Rmult_le_pos; lra).
      nra.
Qed.

Lemma TruncDisk_open : forall R delta, Open (TruncDisk R delta).
Proof.
  intros R delta z [Hmod Hre].
  exists (Rmin (R - Cmod z) (Re z + delta)); split.
  - apply Rmin_pos; lra.
  - intros w Hw. split.
    + (* |w| < R *)
      rewrite <- (Cadd_diff z w).
      eapply Rle_lt_trans; [ apply Cmod_triangle | ].
      apply Rlt_le_trans with (Cmod z + (R - Cmod z)); [ | lra ].
      apply Rplus_lt_compat_l.
      eapply Rlt_le_trans; [ exact Hw | apply Rmin_l ].
    + (* −delta < Re w *)
      assert (HR : Rabs (Re (Cminus w z)) <= Cmod (Cminus w z)) by apply Rabs_Re_le_Cmod.
      assert (Hlt : Cmod (Cminus w z) < Re z + delta)
        by (eapply Rlt_le_trans; [ exact Hw | apply Rmin_r ]).
      rewrite Re_Cminus in HR.
      assert (HR2 : Rabs (Re w - Re z) < Re z + delta)
        by (eapply Rle_lt_trans; [ exact HR | exact Hlt ]).
      apply Rabs_def2 in HR2. lra.
  Qed.

Print Assumptions TruncDisk_convex.
Print Assumptions TruncDisk_open.
