(* ================================================================= *)
(*  PsiXDeriv3.v  --  Psi(e^x) to third order, with bounds.            *)
(*                                                                    *)
(*    D1G = -Sig 1        D2G = Sig 2 - Sig 1                          *)
(*    D3G = -Sig 3 + 3 Sig 2 - Sig 1                                   *)
(*                                                                    *)
(*  Stage 2, part 3.  Simpson needs the third derivative of the        *)
(*  integrand to EXIST and to be LIPSCHITZ.  Because XMomentSum        *)
(*  supplies the single recursion Sig i ' = i Sig i - Sig (i+1), each  *)
(*  order here is one application of derivable_pt_lim_opp or _minus:   *)
(*  the analysis was all done there, and what is left is arithmetic.   *)
(*                                                                    *)
(*  NOTE ON DOMAINS.  Every derivative statement is at x >= 0, which   *)
(*  is all the quadrature needs, and it is what lets the chain start   *)
(*  from the EXISTING GPsi_deriv rather than from a local-             *)
(*  extensionality argument: GPsi and Sig 0 agree only on x >= -1/2,   *)
(*  so a derivative of GPsi at 0 could not be read off Sig 0 without   *)
(*  one.  From the second order on, the functions ARE the Sig          *)
(*  combinations by definition, so no transport is needed at all.      *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi ThetaTailSharp CertifiedPi ThetaDerivMajorant
        ThetaDeriv ThetaDeriv2 PsiXDeriv XMomentMajorant XMomentSum LipCalc.
Open Scope R_scope.

Definition D1G (x : R) : R := - Sig 1 x.
Definition D2G (x : R) : R := Sig 2 x - Sig 1 x.
Definition D3G (x : R) : R := - Sig 3 x + 3 * Sig 2 x - Sig 1 x.

(* order 1 : the bridge to what already exists *)
Lemma D1G_eq_DG : forall x, 0 <= x -> D1G x = DG x.
Proof.
  intros x Hx. unfold D1G. rewrite (Sig1_eq_DG x Hx). ring.
Qed.

Theorem GPsi_deriv1 : forall x, 0 <= x -> derivable_pt_lim GPsi x (D1G x).
Proof.
  intros x Hx. rewrite (D1G_eq_DG x Hx). apply GPsi_deriv; exact Hx.
Qed.

(* orders 2 and 3 : pure arithmetic on the recursion *)
Theorem D1G_deriv : forall x, - / 4 <= x -> derivable_pt_lim D1G x (D2G x).
Proof.
  intros x Hx. unfold D1G, D2G.
  pose proof (Sig_deriv 1 x ltac:(lia) Hx) as H.
  replace (Sig 2 x - Sig 1 x) with (- (INR 1 * Sig 1 x - Sig 2 x))
    by (simpl; ring).
  apply derivable_pt_lim_opp. exact H.
Qed.

Theorem D2G_deriv : forall x, - / 4 <= x -> derivable_pt_lim D2G x (D3G x).
Proof.
  intros x Hx. unfold D2G, D3G.
  pose proof (Sig_deriv 2 x ltac:(lia) Hx) as H2.
  pose proof (Sig_deriv 1 x ltac:(lia) Hx) as H1.
  replace (- Sig 3 x + 3 * Sig 2 x - Sig 1 x)
    with ((INR 2 * Sig 2 x - Sig 3 x) - (INR 1 * Sig 1 x - Sig 2 x))
    by (simpl; ring).
  apply derivable_pt_lim_minus; assumption.
Qed.

(* Order 4 exists too, and for free: Sig 4 is already in range, so the *)
(* recursion supplies D3G's derivative like any other.  That removes   *)
(* the need for the ThetaDeriv2 trick (Lipschitz-without-a-CVU-pass)   *)
(* entirely -- LipOn D3G comes straight from lip_of_deriv on D4G.      *)
(* Note D4G = Sig 4 - 6 Sig 3 + 7 Sig 2 - Sig 1 reproduces the         *)
(* Stirling row 1,7,6,1, which is the correctness oracle.              *)
Definition D4G (x : R) : R := Sig 4 x - 6 * Sig 3 x + 7 * Sig 2 x - Sig 1 x.

Theorem D3G_deriv : forall x, - / 4 <= x -> derivable_pt_lim D3G x (D4G x).
Proof.
  intros x Hx. unfold D3G, D4G.
  pose proof (Sig_deriv 3 x ltac:(lia) Hx) as H3.
  pose proof (Sig_deriv 2 x ltac:(lia) Hx) as H2.
  pose proof (Sig_deriv 1 x ltac:(lia) Hx) as H1.
  replace (Sig 4 x - 6 * Sig 3 x + 7 * Sig 2 x - Sig 1 x)
    with (- (INR 3 * Sig 3 x - Sig 4 x)
          + 3 * (INR 2 * Sig 2 x - Sig 3 x)
          - (INR 1 * Sig 1 x - Sig 2 x)) by (simpl; ring).
  apply derivable_pt_lim_minus.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_opp. exact H3.
    + apply (derivable_pt_lim_scal (Sig 2) 3 x). exact H2.
  - exact H1.
Qed.

(* ----------------------------------------------------------------- *)
(*  BOUNDS.  Every one is taken JOINTLY with the integrand's e^{x/4}   *)
(*  weight, so that the two factors are never maximised separately at  *)
(*  opposite ends of [0,L] -- the mistake that cost a factor e^{L/4}   *)
(*  at order 1 and would cost e^{3L/4} here.                          *)
(*                                                                    *)
(*  Head terms k = 1, 2 are evaluated exactly; k >= 3 is geometric.    *)
(*  At k = 1 the joint threshold i + 1/4 <= pi fails for i = 3, 4, so  *)
(*  those two carry a slack factor e^{sl i} (see XMomentMajorant).     *)
(* ----------------------------------------------------------------- *)
Definition sl (i : nat) : R :=
  match i with 3%nat => / 100 | 4%nat => / 2 | _ => 0 end.

Lemma sl_nonneg : forall i, 0 <= sl i.
Proof.
  intro i. destruct i as [|[|[|[|[|i]]]]]; unfold sl; try lra;
    (apply Rlt_le; apply Rinv_0_lt_compat; lra).
Qed.

Definition KM (i : nat) : R :=
  PI ^ i * exp (- PI) * exp (sl i)
  + (4 * PI) ^ i * exp (- (4 * PI))
  + Cm i * Ktail.

(* the geometric decay past k = 3, for every order at once *)
Lemma tail_geo : forall j : nat,
  exp (- (PI * (INR j + 3) ^ 2 / 2)) <= exp (- (9 * PI / 2)) * exp (- PI) ^ j.
Proof.
  intro j. pose proof PI_RGT_0 as HPI. pose proof (pos_INR j) as Hj.
  assert (Epow : exp (- PI) ^ j = exp (INR j * - PI)) by apply exp_INR_pow.
  rewrite Epow, <- exp_plus. apply exp_le_compat.
  assert (Hq : 0 <= PI * (INR j ^ 2 + 4 * INR j) / 2)
    by (apply Rmult_le_pos; [ nra | lra ]).
  assert (E : PI * (INR j ^ 2 + 4 * INR j) / 2
            = (- (9 * PI / 2) + INR j * - PI)
              - (- (PI * (INR j + 3) ^ 2 / 2))) by field.
  lra.
Qed.

Lemma mterm_tail_Qe : forall i j x, (i <= 4)%nat -> 0 <= x ->
  mterm i x (2 + j) * exp (/ 4 * x)
  <= Cm i * (exp (- (9 * PI / 2)) * exp (- PI) ^ j).
Proof.
  intros i j x Hi Hx. pose proof PI_RGT_0 as HPI.
  assert (Hk : INR (S (2 + j)) = INR j + 3)
    by (rewrite !S_INR, plus_INR; simpl; ring).
  pose proof (pos_INR j) as Hj0.
  assert (H9 : 9 <= (INR j + 3) ^ 2) by nra.
  set (a := PI * (INR j + 3) ^ 2).
  assert (Ha9 : 9 * PI <= a) by (unfold a; nra).
  assert (Ha : 0 < a) by lra.
  assert (Hbig : INR i + / 4 <= a).
  { assert (Hi4 : INR i <= 4)
      by (apply (le_INR i 4) in Hi; simpl in Hi; lra).
    pose proof PI_lower as HP3. lra. }
  (* joint maximum at x = 0 *)
  assert (Hjoint : mterm i x (2 + j) * exp (/ 4 * x) <= a ^ i * exp (- a)).
  { unfold mterm. rewrite Hk. fold a.
    apply mterm_joint_at0_clean; assumption. }
  (* then geometric *)
  assert (Hsplit : exp (- a) = exp (- (a / 2)) * exp (- (a / 2)))
    by (rewrite <- exp_plus; f_equal; lra).
  assert (Hpoly : a ^ i * exp (- (a / 2)) <= Cm i)
    by (apply wpow_half; [ exact Hi | lra ]).
  assert (Hgeo : exp (- (a / 2)) <= exp (- (9 * PI / 2)) * exp (- PI) ^ j)
    by (unfold a; apply tail_geo).
  assert (He : 0 < exp (- (a / 2))) by apply exp_pos.
  assert (Hai : 0 <= a ^ i) by (apply pow_le; lra).
  assert (Hchain : a ^ i * exp (- a) <= Cm i * (exp (- (9 * PI / 2)) * exp (- PI) ^ j)).
  { rewrite Hsplit.
    replace (a ^ i * (exp (- (a / 2)) * exp (- (a / 2))))
      with ((a ^ i * exp (- (a / 2))) * exp (- (a / 2))) by ring.
    apply Rle_trans with (Cm i * exp (- (a / 2))).
    - apply Rmult_le_compat_r; [ lra | exact Hpoly ].
    - apply Rmult_le_compat_l; [ left; apply Cm_pos | exact Hgeo ]. }
  lra.
Qed.

(* the two head terms, k = 1 (a = pi) and k = 2 (a = 4 pi) *)
(* k = 1 (a = pi).  Orders 0..2 clear the joint threshold i + 1/4 <= pi *)
(* outright and use the CLEAN lemma (their sl is 0, so exp (sl i) = 1); *)
(* orders 3 and 4 fall short by 0.108 and 1.108 and pay the slack.      *)
Lemma mterm_head0_Qe : forall i x, (i <= 4)%nat -> 0 <= x ->
  mterm i x 0 * exp (/ 4 * x) <= PI ^ i * exp (- PI) * exp (sl i).
Proof.
  intros i x Hi Hx. pose proof PI_RGT_0 as HPI.
  pose proof PI_lower as HP3. pose proof PI_upper as HP4.
  assert (Ea : PI * INR 1 ^ 2 = PI) by (rewrite INR_S0; ring).
  unfold mterm. rewrite Ea.
  destruct i as [|[|[|[|[|i]]]]].
  - cbn [sl]. rewrite exp_0, Rmult_1_r.
    apply mterm_joint_at0_clean; [ exact Hx | lra | simpl INR; lra ].
  - cbn [sl]. rewrite exp_0, Rmult_1_r.
    apply mterm_joint_at0_clean; [ exact Hx | lra | simpl INR; lra ].
  - cbn [sl]. rewrite exp_0, Rmult_1_r.
    apply mterm_joint_at0_clean; [ exact Hx | lra | simpl INR; lra ].
  - (* i = 3 : (3.25 - pi)^2 = 0.01175 <= pi/100 = 0.03142 *)
    apply mterm_joint_at0; [ exact Hx | lra | cbn [sl]; lra | ].
    cbn [sl]. simpl INR.
    replace (0 + 1 + 1 + 1 + / 4 - PI) with (3 + / 4 - PI) by ring.
    assert (Hd : 3 + / 4 - PI <= 11 / 100) by lra.
    assert (Hd0 : 0 <= 3 + / 4 - PI) by lra.
    nra.
  - (* i = 4 : (4.25 - pi)^2 = 1.2286 <= pi/2 = 1.5708 *)
    apply mterm_joint_at0; [ exact Hx | lra | cbn [sl]; lra | ].
    cbn [sl]. simpl INR.
    replace (0 + 1 + 1 + 1 + 1 + / 4 - PI) with (4 + / 4 - PI) by ring.
    assert (Hd : 4 + / 4 - PI <= 111 / 100) by lra.
    assert (Hd0 : 0 <= 4 + / 4 - PI) by lra.
    nra.
  - exfalso; lia.
Qed.

Lemma mterm_head1_Qe : forall i x, (i <= 4)%nat -> 0 <= x ->
  mterm i x 1 * exp (/ 4 * x) <= (4 * PI) ^ i * exp (- (4 * PI)).
Proof.
  intros i x Hi Hx. pose proof PI_RGT_0 as HPI. pose proof PI_lower as HP3.
  assert (Ea : PI * INR 2 ^ 2 = 4 * PI) by (rewrite INR_S1; ring).
  unfold mterm. rewrite Ea.
  apply mterm_joint_at0_clean; try lra.
  assert (Hi4 : INR i <= 4)
    by (apply (le_INR i 4) in Hi; simpl in Hi; lra).
  lra.
Qed.

(* the head/tail split, exactly the shape sharp_sum_bound uses *)
Lemma mpartial_Qe_bound : forall i x N, (i <= 4)%nat -> 0 <= x ->
  mpartial i x N * exp (/ 4 * x) <= KM i.
Proof.
  intros i x N Hi Hx. pose proof qt_bounds as [Hq0 Hq1].
  assert (Hw : 0 < exp (/ 4 * x)) by apply exp_pos.
  assert (E : mpartial i x N * exp (/ 4 * x)
            = sum_f_R0 (fun n => mterm i x n * exp (/ 4 * x)) N).
  { unfold mpartial.
    assert (Ec : sum_f_R0 (mterm i x) N * exp (/ 4 * x)
               = exp (/ 4 * x) * sum_f_R0 (mterm i x) N) by ring.
    rewrite Ec, (scal_sum (mterm i x) N (exp (/ 4 * x))).
    apply sum_eq; intros k Hk; ring. }
  rewrite E.
  pose proof (mterm_head0_Qe i x Hi Hx) as H0.
  pose proof (mterm_head1_Qe i x Hi Hx) as H1.
  assert (Hn1 : 0 <= mterm i x 1 * exp (/ 4 * x))
    by (apply Rmult_le_pos; [ apply mterm_nonneg | lra ]).
  assert (Htail0 : 0 <= Cm i * Ktail).
  { apply Rmult_le_pos; [ left; apply Cm_pos | apply Ktail_nonneg ]. }
  unfold KM.
  destruct (Nat.le_gt_cases N 1) as [Hle | Hgt].
  - assert (Hmono : sum_f_R0 (fun n => mterm i x n * exp (/ 4 * x)) N
                    <= mterm i x 0 * exp (/ 4 * x)
                       + mterm i x 1 * exp (/ 4 * x)).
    { destruct N as [| [| N]].
      - cbn [sum_f_R0]. lra.
      - cbn [sum_f_R0]. lra.
      - exfalso; lia. }
    lra.
  - rewrite (tech2 (fun n => mterm i x n * exp (/ 4 * x)) 1 N Hgt).
    assert (Hhead : sum_f_R0 (fun n => mterm i x n * exp (/ 4 * x)) 1
                    <= PI ^ i * exp (- PI) * exp (sl i)
                       + (4 * PI) ^ i * exp (- (4 * PI)))
      by (cbn [sum_f_R0]; lra).
    assert (Htl : sum_f_R0
                    (fun k => mterm i x (S 1 + k) * exp (/ 4 * x)) (N - S 1)
                  <= Cm i * Ktail).
    { eapply Rle_trans.
      - apply sum_f_R0_le. intro k.
        change (S 1 + k)%nat with (2 + k)%nat.
        apply mterm_tail_Qe; assumption.
      - assert (Eg : sum_f_R0
                       (fun k => Cm i * (exp (- (9 * PI / 2)) * exp (- PI) ^ k))
                       (N - S 1)
                   = Cm i * exp (- (9 * PI / 2))
                     * sum_f_R0 (fun k => exp (- PI) ^ k) (N - S 1)).
        { rewrite (scal_sum (fun k => exp (- PI) ^ k) (N - S 1)
                     (Cm i * exp (- (9 * PI / 2)))).
          apply sum_eq; intros k Hk; ring. }
        rewrite Eg. unfold Ktail, qt, Rdiv.
        assert (Hgp : sum_f_R0 (fun k => exp (- PI) ^ k) (N - S 1)
                   <= / (1 - exp (- PI)))
          by (apply geom_partial_bound; unfold qt in *; lra).
        assert (Hc : 0 <= Cm i * exp (- (9 * PI / 2)))
          by (pose proof (Cm_pos i); pose proof (exp_pos (- (9 * PI / 2))); nra).
        assert (Hstep : Cm i * exp (- (9 * PI / 2))
                          * sum_f_R0 (fun k => exp (- PI) ^ k) (N - S 1)
                     <= Cm i * exp (- (9 * PI / 2)) * / (1 - exp (- PI)))
          by (apply Rmult_le_compat_l; assumption).
        lra. }
    lra.
Qed.

Theorem Sig_Qe_bound : forall i x, (i <= 4)%nat -> 0 <= x ->
  Sig i x * exp (/ 4 * x) <= KM i.
Proof.
  intros i x Hi Hx.
  assert (Hx2 : - / 2 <= x) by lra.
  assert (Hcv : Un_cv (fun N => mpartial i x N * exp (/ 4 * x))
                  (Sig i x * exp (/ 4 * x)))
    by (apply CV_mult; [ apply Sig_spec; assumption | apply Un_cv_const' ]).
  eapply Rle_cv_lim.
  2: exact Hcv.
  2: apply Un_cv_const'.
  intro N. apply mpartial_Qe_bound; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  The derivative bounds, jointly with the weight.  Each is the same  *)
(*  integer combination as the derivative itself, with signs made      *)
(*  positive by the triangle inequality.                              *)
(* ----------------------------------------------------------------- *)
Definition B0 : R := KM 0.
Definition B1 : R := KM 1.
Definition B2 : R := KM 2 + KM 1.
Definition B3 : R := KM 3 + 3 * KM 2 + KM 1.
Definition B4 : R := KM 4 + 6 * KM 3 + 7 * KM 2 + KM 1.

Lemma KM_nonneg : forall i, (i <= 4)%nat -> 0 <= KM i.
Proof.
  intros i Hi. unfold KM. pose proof PI_RGT_0.
  pose proof (Cm_pos i). pose proof Ktail_nonneg.
  assert (V1 : 0 <= PI ^ i * exp (- PI) * exp (sl i)).
  { repeat apply Rmult_le_pos;
      [ apply pow_le; lra | left; apply exp_pos | left; apply exp_pos ]. }
  assert (V2 : 0 <= (4 * PI) ^ i * exp (- (4 * PI)))
    by (apply Rmult_le_pos; [ apply pow_le; lra | left; apply exp_pos ]).
  assert (V3 : 0 <= Cm i * Ktail) by (apply Rmult_le_pos; lra).
  lra.
Qed.

Lemma B_nonneg : 0 <= B0 /\ 0 <= B1 /\ 0 <= B2 /\ 0 <= B3 /\ 0 <= B4.
Proof.
  pose proof (KM_nonneg 0 ltac:(lia)). pose proof (KM_nonneg 1 ltac:(lia)).
  pose proof (KM_nonneg 2 ltac:(lia)). pose proof (KM_nonneg 3 ltac:(lia)).
  pose proof (KM_nonneg 4 ltac:(lia)).
  unfold B0, B1, B2, B3, B4. repeat split; lra.
Qed.

(* GPsi itself: Sig 0, so the bound is immediate *)
Theorem GPsi_Qe_bdd : forall L, BddOn (fun x => GPsi x * exp (/ 4 * x)) 0 L B0.
Proof.
  intros L x Hx. destruct Hx as [Hx0 _].
  assert (Hx2 : - / 2 <= x) by lra.
  rewrite <- (Sig0_eq_GPsi x Hx2).
  assert (Hnn : 0 <= Sig 0 x * exp (/ 4 * x)).
  { apply Rmult_le_pos;
      [ apply Sig_nonneg; [ lia | exact Hx2 ] | left; apply exp_pos ]. }
  rewrite Rabs_pos_eq by exact Hnn.
  apply Sig_Qe_bound; [ lia | exact Hx0 ].
Qed.

Theorem D1G_Qe_bdd : forall L, BddOn (fun x => D1G x * exp (/ 4 * x)) 0 L B1.
Proof.
  intros L x Hx. destruct Hx as [Hx0 _].
  assert (Hx2 : - / 2 <= x) by lra.
  assert (Hw : 0 < exp (/ 4 * x)) by apply exp_pos.
  assert (Hs : 0 <= Sig 1 x) by (apply Sig_nonneg; [ lia | exact Hx2 ]).
  unfold D1G.
  replace (- Sig 1 x * exp (/ 4 * x)) with (- (Sig 1 x * exp (/ 4 * x))) by ring.
  rewrite Rabs_Ropp, Rabs_pos_eq by (apply Rmult_le_pos; lra).
  apply Sig_Qe_bound; [ lia | exact Hx0 ].
Qed.

Theorem D2G_Qe_bdd : forall L, BddOn (fun x => D2G x * exp (/ 4 * x)) 0 L B2.
Proof.
  intros L x Hx. destruct Hx as [Hx0 _].
  assert (Hx2 : - / 2 <= x) by lra.
  assert (Hw : 0 < exp (/ 4 * x)) by apply exp_pos.
  pose proof (Sig_Qe_bound 1 x ltac:(lia) Hx0) as S1.
  pose proof (Sig_Qe_bound 2 x ltac:(lia) Hx0) as S2.
  assert (N1 : 0 <= Sig 1 x * exp (/ 4 * x))
    by (apply Rmult_le_pos;
        [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  assert (N2 : 0 <= Sig 2 x * exp (/ 4 * x))
    by (apply Rmult_le_pos;
        [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  unfold D2G, B2.
  replace ((Sig 2 x - Sig 1 x) * exp (/ 4 * x))
    with (Sig 2 x * exp (/ 4 * x) - Sig 1 x * exp (/ 4 * x)) by ring.
  apply Rabs_le. split; lra.
Qed.

Theorem D3G_Qe_bdd : forall L, BddOn (fun x => D3G x * exp (/ 4 * x)) 0 L B3.
Proof.
  intros L x Hx. destruct Hx as [Hx0 _].
  assert (Hx2 : - / 2 <= x) by lra.
  assert (Hw : 0 < exp (/ 4 * x)) by apply exp_pos.
  pose proof (Sig_Qe_bound 1 x ltac:(lia) Hx0) as S1.
  pose proof (Sig_Qe_bound 2 x ltac:(lia) Hx0) as S2.
  pose proof (Sig_Qe_bound 3 x ltac:(lia) Hx0) as S3.
  assert (N1 : 0 <= Sig 1 x * exp (/ 4 * x))
    by (apply Rmult_le_pos;
        [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  assert (N2 : 0 <= Sig 2 x * exp (/ 4 * x))
    by (apply Rmult_le_pos;
        [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  assert (N3 : 0 <= Sig 3 x * exp (/ 4 * x))
    by (apply Rmult_le_pos;
        [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  unfold D3G, B3.
  replace ((- Sig 3 x + 3 * Sig 2 x - Sig 1 x) * exp (/ 4 * x))
    with (- (Sig 3 x * exp (/ 4 * x)) + 3 * (Sig 2 x * exp (/ 4 * x))
          - Sig 1 x * exp (/ 4 * x)) by ring.
  apply Rabs_le. split; lra.
Qed.

Theorem D4G_Qe_bdd : forall L, BddOn (fun x => D4G x * exp (/ 4 * x)) 0 L B4.
Proof.
  intros L x Hx. destruct Hx as [Hx0 _].
  assert (Hx2 : - / 2 <= x) by lra.
  assert (Hw : 0 < exp (/ 4 * x)) by apply exp_pos.
  pose proof (Sig_Qe_bound 1 x ltac:(lia) Hx0) as S1.
  pose proof (Sig_Qe_bound 2 x ltac:(lia) Hx0) as S2.
  pose proof (Sig_Qe_bound 3 x ltac:(lia) Hx0) as S3.
  pose proof (Sig_Qe_bound 4 x ltac:(lia) Hx0) as S4.
  assert (N1 : 0 <= Sig 1 x * exp (/ 4 * x))
    by (apply Rmult_le_pos; [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  assert (N2 : 0 <= Sig 2 x * exp (/ 4 * x))
    by (apply Rmult_le_pos; [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  assert (N3 : 0 <= Sig 3 x * exp (/ 4 * x))
    by (apply Rmult_le_pos; [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  assert (N4 : 0 <= Sig 4 x * exp (/ 4 * x))
    by (apply Rmult_le_pos; [ apply Sig_nonneg; [ lia | exact Hx2 ] | lra ]).
  unfold D4G, B4.
  replace ((Sig 4 x - 6 * Sig 3 x + 7 * Sig 2 x - Sig 1 x) * exp (/ 4 * x))
    with (Sig 4 x * exp (/ 4 * x) - 6 * (Sig 3 x * exp (/ 4 * x))
          + 7 * (Sig 2 x * exp (/ 4 * x)) - Sig 1 x * exp (/ 4 * x)) by ring.
  apply Rabs_le. split; lra.
Qed.

Print Assumptions GPsi_deriv1.
Print Assumptions D3G_deriv.
Print Assumptions Sig_Qe_bound.
Print Assumptions D3G_Qe_bdd.
Print Assumptions D4G_Qe_bdd.
Print Assumptions D1G_deriv.
Print Assumptions D2G_deriv.
