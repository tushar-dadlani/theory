(* ================================================================= *)
(*  IntegrandLip4.v  --  the integrand to fourth order, and M4fin.     *)
(*                                                                    *)
(*    G1 G2 G3 G4     the derivatives of gint t                        *)
(*    d3gint_lip      LipOn (G3 t) 0 L (M4fin t L)                     *)
(*    gint_simpson    SimpsonQuad's bound, instantiated at gint        *)
(*                                                                    *)
(*  Stage 3.  Everything here is Leibniz over gint t = P . Ct t with   *)
(*  P = GPsi . Qe, assembled from PsiXDeriv3's four orders.  Two       *)
(*  layers of binomial bookkeeping and nothing else:                   *)
(*                                                                    *)
(*    P^(j)   = Qe . sum_m C(j,m) (1/4)^(j-m) GPsi^(m)                 *)
(*    gint^(j) = sum_m C(j,m) P^(m) Ct^(j-m)                           *)
(*                                                                    *)
(*  The Ct factors contribute |Ct^(m)| <= T^m with T = |t|/2, so the   *)
(*  final constant is the plain binomial                              *)
(*                                                                    *)
(*    M4fin = A4 + 4 A3 T + 6 A2 T^2 + 4 A1 T^3 + A0 T^4.              *)
(*                                                                    *)
(*  Every A_j is JOINT -- it bounds |GPsi^(j) . Qe| in one go, never   *)
(*  sup|GPsi^(j)| times sup|Qe|.  That is what keeps M4fin near the    *)
(*  truth: at t = 22 it is about 2040 against a true 1477, a factor    *)
(*  1.38.  Paying EL factorwise instead would give roughly 3100 and    *)
(*  breach the budget the n = 512 run needs.                          *)
(*                                                                    *)
(*  Note the Lipschitz constant for the THIRD derivative comes from a  *)
(*  genuine bound on the FOURTH, via lip_of_deriv -- possible only     *)
(*  because PsiXDeriv3 gets order 4 for free out of the same moment    *)
(*  recursion.  Axiom-clean.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Ranalysis5 Lra Lia.
Require Import JacobiTheta RiemannPsi CertifiedPi
        ThetaDeriv PsiXDeriv XMomentMajorant XMomentSum PsiXDeriv3
        LipCalc IntegrandLip SimpsonQuad.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the two extra cosine derivatives                              *)
(* ----------------------------------------------------------------- *)
Definition Ct3 (t x : R) : R := t / 2 * (t / 2 * (t / 2 * sin (t / 2 * x))).
Definition Ct4 (t x : R) : R :=
  t / 2 * (t / 2 * (t / 2 * (t / 2 * cos (t / 2 * x)))).

Lemma Ct''_deriv : forall t x, derivable_pt_lim (Ct'' t) x (Ct3 t x).
Proof.
  intros t x. unfold Ct'', Ct3.
  apply (derivable_pt_lim_ext
           (mult_real_fct (- (t / 2 * (t / 2))) (fun s => cos (t / 2 * s)))).
  - intro z. unfold mult_real_fct. ring.
  - replace (t / 2 * (t / 2 * (t / 2 * sin (t / 2 * x))))
      with (- (t / 2 * (t / 2)) * - (t / 2 * sin (t / 2 * x))) by ring.
    apply derivable_pt_lim_scal. apply dcos_scal.
Qed.

Lemma Ct3_deriv : forall t x, derivable_pt_lim (Ct3 t) x (Ct4 t x).
Proof.
  intros t x. unfold Ct3, Ct4.
  apply (derivable_pt_lim_ext
           (mult_real_fct (t / 2 * (t / 2 * (t / 2))) (fun s => sin (t / 2 * s)))).
  - intro z. unfold mult_real_fct. ring.
  - replace (t / 2 * (t / 2 * (t / 2 * (t / 2 * cos (t / 2 * x)))))
      with (t / 2 * (t / 2 * (t / 2)) * (t / 2 * cos (t / 2 * x))) by ring.
    apply derivable_pt_lim_scal. apply dsin_scal.
Qed.

Lemma Ct3_bdd : forall t L, BddOn (Ct3 t) 0 L (Tt t * (Tt t * Tt t)).
Proof.
  intros t L x _. unfold Ct3, Tt.
  rewrite !Rabs_mult, !Rabs_half.
  pose proof (abs_sin_le1 (t / 2 * x)) as Hs.
  pose proof (Rabs_pos t) as Ht.
  pose proof (Rabs_pos (sin (t / 2 * x))) as Hsp.
  set (T := Rabs t / 2). assert (HT : 0 <= T) by (unfold T; lra).
  apply Rle_trans with (T * (T * (T * 1))); [ | right; ring ].
  repeat (apply Rmult_le_compat_l; [ lra | ]). exact Hs.
Qed.

Lemma Ct4_bdd : forall t L, BddOn (Ct4 t) 0 L (Tt t * (Tt t * (Tt t * Tt t))).
Proof.
  intros t L x _. unfold Ct4, Tt.
  rewrite !Rabs_mult, !Rabs_half.
  pose proof (abs_cos_le1 (t / 2 * x)) as Hc.
  pose proof (Rabs_pos t) as Ht.
  set (T := Rabs t / 2). assert (HT : 0 <= T) by (unfold T; lra).
  apply Rle_trans with (T * (T * (T * (T * 1)))); [ | right; ring ].
  repeat (apply Rmult_le_compat_l; [ lra | ]). exact Hc.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the profile P = GPsi . Qe and its four derivatives             *)
(*                                                                    *)
(*  P^(j) = Qe . sum_m C(j,m) (1/4)^(j-m) GPsi^(m), because Qe' = Qe/4. *)
(* ----------------------------------------------------------------- *)
Definition PG0 (x : R) : R := GPsi x * Qe x.
Definition PG1 (x : R) : R := (D1G x + / 4 * GPsi x) * Qe x.
Definition PG2 (x : R) : R := (D2G x + / 2 * D1G x + / 16 * GPsi x) * Qe x.
Definition PG3 (x : R) : R :=
  (D3G x + 3 / 4 * D2G x + 3 / 16 * D1G x + / 64 * GPsi x) * Qe x.
Definition PG4 (x : R) : R :=
  (D4G x + D3G x + 3 / 8 * D2G x + / 16 * D1G x + / 256 * GPsi x) * Qe x.

Lemma PG0_deriv : forall x, 0 <= x -> derivable_pt_lim PG0 x (PG1 x).
Proof.
  intros x Hx. unfold PG0, PG1.
  pose proof (derivable_pt_lim_mult GPsi Qe x (D1G x) (Qe' x)
                (GPsi_deriv1 x Hx) (Qe_deriv x)) as H.
  replace ((D1G x + / 4 * GPsi x) * Qe x)
    with (D1G x * Qe x + GPsi x * Qe' x) by (unfold Qe'; ring).
  exact H.
Qed.

Lemma PG1_deriv : forall x, 0 <= x -> derivable_pt_lim PG1 x (PG2 x).
Proof.
  intros x Hx. assert (Hx4 : - / 4 <= x) by lra.
  unfold PG1, PG2.
  assert (Hs : derivable_pt_lim (fun y => D1G y + / 4 * GPsi y) x
                 (D2G x + / 4 * D1G x)).
  { apply derivable_pt_lim_plus.
    - apply D1G_deriv; exact Hx4.
    - apply (derivable_pt_lim_scal GPsi (/ 4) x (D1G x)).
      apply GPsi_deriv1; exact Hx. }
  pose proof (derivable_pt_lim_mult (fun y => D1G y + / 4 * GPsi y) Qe x
                (D2G x + / 4 * D1G x) (Qe' x) Hs (Qe_deriv x)) as H.
  replace ((D2G x + / 2 * D1G x + / 16 * GPsi x) * Qe x)
    with ((D2G x + / 4 * D1G x) * Qe x
          + (D1G x + / 4 * GPsi x) * Qe' x) by (unfold Qe'; field).
  exact H.
Qed.

Lemma PG2_deriv : forall x, 0 <= x -> derivable_pt_lim PG2 x (PG3 x).
Proof.
  intros x Hx. assert (Hx4 : - / 4 <= x) by lra.
  unfold PG2, PG3.
  assert (Hs : derivable_pt_lim
                 (fun y => D2G y + / 2 * D1G y + / 16 * GPsi y) x
                 (D3G x + / 2 * D2G x + / 16 * D1G x)).
  { apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_plus.
      + apply D2G_deriv; exact Hx4.
      + apply (derivable_pt_lim_scal D1G (/ 2) x (D2G x)).
        apply D1G_deriv; exact Hx4.
    - apply (derivable_pt_lim_scal GPsi (/ 16) x (D1G x)).
      apply GPsi_deriv1; exact Hx. }
  pose proof (derivable_pt_lim_mult
                (fun y => D2G y + / 2 * D1G y + / 16 * GPsi y) Qe x
                (D3G x + / 2 * D2G x + / 16 * D1G x) (Qe' x) Hs (Qe_deriv x)) as H.
  replace ((D3G x + 3 / 4 * D2G x + 3 / 16 * D1G x + / 64 * GPsi x) * Qe x)
    with ((D3G x + / 2 * D2G x + / 16 * D1G x) * Qe x
          + (D2G x + / 2 * D1G x + / 16 * GPsi x) * Qe' x)
    by (unfold Qe'; field).
  exact H.
Qed.

Lemma PG3_deriv : forall x, 0 <= x -> derivable_pt_lim PG3 x (PG4 x).
Proof.
  intros x Hx. assert (Hx4 : - / 4 <= x) by lra.
  unfold PG3, PG4.
  assert (Hs : derivable_pt_lim
                 (fun y => D3G y + 3 / 4 * D2G y + 3 / 16 * D1G y
                           + / 64 * GPsi y) x
                 (D4G x + 3 / 4 * D3G x + 3 / 16 * D2G x + / 64 * D1G x)).
  { apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_plus.
      + apply derivable_pt_lim_plus.
        * apply D3G_deriv; exact Hx4.
        * apply (derivable_pt_lim_scal D2G (3 / 4) x (D3G x)).
          apply D2G_deriv; exact Hx4.
      + apply (derivable_pt_lim_scal D1G (3 / 16) x (D2G x)).
        apply D1G_deriv; exact Hx4.
    - apply (derivable_pt_lim_scal GPsi (/ 64) x (D1G x)).
      apply GPsi_deriv1; exact Hx. }
  pose proof (derivable_pt_lim_mult
                (fun y => D3G y + 3 / 4 * D2G y + 3 / 16 * D1G y
                          + / 64 * GPsi y) Qe x
                (D4G x + 3 / 4 * D3G x + 3 / 16 * D2G x + / 64 * D1G x)
                (Qe' x) Hs (Qe_deriv x)) as H.
  replace ((D4G x + D3G x + 3 / 8 * D2G x + / 16 * D1G x
            + / 256 * GPsi x) * Qe x)
    with ((D4G x + 3 / 4 * D3G x + 3 / 16 * D2G x + / 64 * D1G x) * Qe x
          + (D3G x + 3 / 4 * D2G x + 3 / 16 * D1G x + / 64 * GPsi x) * Qe' x)
    by (unfold Qe'; field).
  exact H.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  bounds on the profile.  Note NONE of A0..A4 mentions L: the    *)
(*  joint bounds of PsiXDeriv3 already absorbed the weight, so there   *)
(*  is no e^{L/4} anywhere.                                            *)
(* ----------------------------------------------------------------- *)
Definition A0 : R := B0.
Definition A1 : R := B1 + / 4 * B0.
Definition A2 : R := B2 + / 2 * B1 + / 16 * B0.
Definition A3 : R := B3 + 3 / 4 * B2 + 3 / 16 * B1 + / 64 * B0.
Definition A4 : R := B4 + B3 + 3 / 8 * B2 + / 16 * B1 + / 256 * B0.

Lemma abs_prod_le : forall u v U V,
  Rabs u <= U -> Rabs v <= V -> Rabs (u * v) <= U * V.
Proof.
  intros u v U V Hu Hv. rewrite Rabs_mult.
  apply Rmult_le_compat; try apply Rabs_pos; assumption.
Qed.

Lemma abs_scal_le : forall c u U, 0 <= c -> Rabs u <= U -> Rabs (c * u) <= c * U.
Proof.
  intros c u U Hc Hu. rewrite Rabs_mult, (Rabs_pos_eq c) by exact Hc.
  apply Rmult_le_compat_l; assumption.
Qed.

Lemma abs2 : forall a b A B, Rabs a <= A -> Rabs b <= B -> Rabs (a + b) <= A + B.
Proof. intros. eapply Rle_trans; [ apply Rabs_triang | lra ]. Qed.

Lemma abs3 : forall a b c A B C,
  Rabs a <= A -> Rabs b <= B -> Rabs c <= C -> Rabs (a + b + c) <= A + B + C.
Proof.
  intros. eapply Rle_trans; [ apply Rabs_triang | ].
  pose proof (abs2 a b A B). lra.
Qed.

Lemma abs4 : forall a b c d A B C D,
  Rabs a <= A -> Rabs b <= B -> Rabs c <= C -> Rabs d <= D ->
  Rabs (a + b + c + d) <= A + B + C + D.
Proof.
  intros. eapply Rle_trans; [ apply Rabs_triang | ].
  pose proof (abs3 a b c A B C). lra.
Qed.

Lemma abs5 : forall a b c d e A B C D E,
  Rabs a <= A -> Rabs b <= B -> Rabs c <= C -> Rabs d <= D -> Rabs e <= E ->
  Rabs (a + b + c + d + e) <= A + B + C + D + E.
Proof.
  intros. eapply Rle_trans; [ apply Rabs_triang | ].
  pose proof (abs4 a b c d A B C D). lra.
Qed.

Lemma PG0_bdd : forall L, BddOn PG0 0 L A0.
Proof. intros L x Hx. unfold PG0, Qe, A0. exact (GPsi_Qe_bdd L x Hx). Qed.

Lemma PG1_bdd : forall L, BddOn PG1 0 L A1.
Proof.
  intros L x Hx. unfold PG1, A1, Qe.
  pose proof (D1G_Qe_bdd L x Hx) as H1; cbv beta in H1.
  pose proof (GPsi_Qe_bdd L x Hx) as H0; cbv beta in H0.
  replace ((D1G x + / 4 * GPsi x) * exp (/ 4 * x))
    with (D1G x * exp (/ 4 * x) + / 4 * (GPsi x * exp (/ 4 * x))) by ring.
  apply abs2; [ exact H1 | apply abs_scal_le; [ lra | exact H0 ] ].
Qed.

Lemma PG2_bdd : forall L, BddOn PG2 0 L A2.
Proof.
  intros L x Hx. unfold PG2, A2, Qe.
  pose proof (D2G_Qe_bdd L x Hx) as H2; cbv beta in H2.
  pose proof (D1G_Qe_bdd L x Hx) as H1; cbv beta in H1.
  pose proof (GPsi_Qe_bdd L x Hx) as H0; cbv beta in H0.
  replace ((D2G x + / 2 * D1G x + / 16 * GPsi x) * exp (/ 4 * x))
    with (D2G x * exp (/ 4 * x) + / 2 * (D1G x * exp (/ 4 * x))
          + / 16 * (GPsi x * exp (/ 4 * x))) by ring.
  apply abs3; [ exact H2 | apply abs_scal_le; [ lra | exact H1 ]
              | apply abs_scal_le; [ lra | exact H0 ] ].
Qed.

Lemma PG3_bdd : forall L, BddOn PG3 0 L A3.
Proof.
  intros L x Hx. unfold PG3, A3, Qe.
  pose proof (D3G_Qe_bdd L x Hx) as H3; cbv beta in H3.
  pose proof (D2G_Qe_bdd L x Hx) as H2; cbv beta in H2.
  pose proof (D1G_Qe_bdd L x Hx) as H1; cbv beta in H1.
  pose proof (GPsi_Qe_bdd L x Hx) as H0; cbv beta in H0.
  replace ((D3G x + 3 / 4 * D2G x + 3 / 16 * D1G x + / 64 * GPsi x)
             * exp (/ 4 * x))
    with (D3G x * exp (/ 4 * x) + 3 / 4 * (D2G x * exp (/ 4 * x))
          + 3 / 16 * (D1G x * exp (/ 4 * x))
          + / 64 * (GPsi x * exp (/ 4 * x))) by ring.
  apply abs4; [ exact H3 | apply abs_scal_le; [ lra | exact H2 ]
              | apply abs_scal_le; [ lra | exact H1 ]
              | apply abs_scal_le; [ lra | exact H0 ] ].
Qed.

Lemma PG4_bdd : forall L, BddOn PG4 0 L A4.
Proof.
  intros L x Hx. unfold PG4, A4, Qe.
  pose proof (D4G_Qe_bdd L x Hx) as H4; cbv beta in H4.
  pose proof (D3G_Qe_bdd L x Hx) as H3; cbv beta in H3.
  pose proof (D2G_Qe_bdd L x Hx) as H2; cbv beta in H2.
  pose proof (D1G_Qe_bdd L x Hx) as H1; cbv beta in H1.
  pose proof (GPsi_Qe_bdd L x Hx) as H0; cbv beta in H0.
  replace ((D4G x + D3G x + 3 / 8 * D2G x + / 16 * D1G x + / 256 * GPsi x)
             * exp (/ 4 * x))
    with (D4G x * exp (/ 4 * x) + D3G x * exp (/ 4 * x)
          + 3 / 8 * (D2G x * exp (/ 4 * x))
          + / 16 * (D1G x * exp (/ 4 * x))
          + / 256 * (GPsi x * exp (/ 4 * x))) by ring.
  apply abs5; [ exact H4 | exact H3
              | apply abs_scal_le; [ lra | exact H2 ]
              | apply abs_scal_le; [ lra | exact H1 ]
              | apply abs_scal_le; [ lra | exact H0 ] ].
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the integrand's derivatives: Leibniz over gint t = PG0 . Ct t  *)
(* ----------------------------------------------------------------- *)
Definition G1 (t x : R) : R := PG1 x * Ct t x + PG0 x * Ct' t x.
Definition G2 (t x : R) : R :=
  PG2 x * Ct t x + 2 * (PG1 x * Ct' t x) + PG0 x * Ct'' t x.
Definition G3 (t x : R) : R :=
  PG3 x * Ct t x + 3 * (PG2 x * Ct' t x) + 3 * (PG1 x * Ct'' t x)
  + PG0 x * Ct3 t x.
Definition G4 (t x : R) : R :=
  PG4 x * Ct t x + 4 * (PG3 x * Ct' t x) + 6 * (PG2 x * Ct'' t x)
  + 4 * (PG1 x * Ct3 t x) + PG0 x * Ct4 t x.

Lemma gint_deriv_1 : forall t x, 0 <= x -> derivable_pt_lim (gint t) x (G1 t x).
Proof.
  intros t x Hx.
  pose proof (derivable_pt_lim_mult PG0 (Ct t) x (PG1 x) (Ct' t x)
                (PG0_deriv x Hx) (Ct_deriv t x)) as H.
  unfold gint, G1, PG0 in *. exact H.
Qed.

Lemma gint_deriv_2 : forall t x, 0 <= x -> derivable_pt_lim (G1 t) x (G2 t x).
Proof.
  intros t x Hx. unfold G1, G2.
  pose proof (derivable_pt_lim_mult PG1 (Ct t) x (PG2 x) (Ct' t x)
                (PG1_deriv x Hx) (Ct_deriv t x)) as Ha.
  pose proof (derivable_pt_lim_mult PG0 (Ct' t) x (PG1 x) (Ct'' t x)
                (PG0_deriv x Hx) (Ct'_deriv t x)) as Hb.
  replace (PG2 x * Ct t x + 2 * (PG1 x * Ct' t x) + PG0 x * Ct'' t x)
    with ((PG2 x * Ct t x + PG1 x * Ct' t x)
          + (PG1 x * Ct' t x + PG0 x * Ct'' t x)) by ring.
  apply derivable_pt_lim_plus; assumption.
Qed.

Lemma gint_deriv_3 : forall t x, 0 <= x -> derivable_pt_lim (G2 t) x (G3 t x).
Proof.
  intros t x Hx. unfold G2, G3.
  pose proof (derivable_pt_lim_mult PG2 (Ct t) x (PG3 x) (Ct' t x)
                (PG2_deriv x Hx) (Ct_deriv t x)) as Ha.
  pose proof (derivable_pt_lim_mult PG1 (Ct' t) x (PG2 x) (Ct'' t x)
                (PG1_deriv x Hx) (Ct'_deriv t x)) as Hb.
  pose proof (derivable_pt_lim_mult PG0 (Ct'' t) x (PG1 x) (Ct3 t x)
                (PG0_deriv x Hx) (Ct''_deriv t x)) as Hc.
  replace (PG3 x * Ct t x + 3 * (PG2 x * Ct' t x) + 3 * (PG1 x * Ct'' t x)
           + PG0 x * Ct3 t x)
    with ((PG3 x * Ct t x + PG2 x * Ct' t x)
          + 2 * (PG2 x * Ct' t x + PG1 x * Ct'' t x)
          + (PG1 x * Ct'' t x + PG0 x * Ct3 t x)) by ring.
  apply derivable_pt_lim_plus.
  - apply derivable_pt_lim_plus.
    + exact Ha.
    + apply (derivable_pt_lim_scal (PG1 * Ct' t)%F 2 x). exact Hb.
  - exact Hc.
Qed.

Lemma gint_deriv_4 : forall t x, 0 <= x -> derivable_pt_lim (G3 t) x (G4 t x).
Proof.
  intros t x Hx. unfold G3, G4.
  pose proof (derivable_pt_lim_mult PG3 (Ct t) x (PG4 x) (Ct' t x)
                (PG3_deriv x Hx) (Ct_deriv t x)) as Ha.
  pose proof (derivable_pt_lim_mult PG2 (Ct' t) x (PG3 x) (Ct'' t x)
                (PG2_deriv x Hx) (Ct'_deriv t x)) as Hb.
  pose proof (derivable_pt_lim_mult PG1 (Ct'' t) x (PG2 x) (Ct3 t x)
                (PG1_deriv x Hx) (Ct''_deriv t x)) as Hc.
  pose proof (derivable_pt_lim_mult PG0 (Ct3 t) x (PG1 x) (Ct4 t x)
                (PG0_deriv x Hx) (Ct3_deriv t x)) as Hd.
  replace (PG4 x * Ct t x + 4 * (PG3 x * Ct' t x) + 6 * (PG2 x * Ct'' t x)
           + 4 * (PG1 x * Ct3 t x) + PG0 x * Ct4 t x)
    with ((PG4 x * Ct t x + PG3 x * Ct' t x)
          + 3 * (PG3 x * Ct' t x + PG2 x * Ct'' t x)
          + 3 * (PG2 x * Ct'' t x + PG1 x * Ct3 t x)
          + (PG1 x * Ct3 t x + PG0 x * Ct4 t x)) by ring.
  apply derivable_pt_lim_plus.
  - apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_plus.
      * exact Ha.
      * apply (derivable_pt_lim_scal (PG2 * Ct' t)%F 3 x). exact Hb.
    + apply (derivable_pt_lim_scal (PG1 * Ct'' t)%F 3 x). exact Hc.
  - exact Hd.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE CONSTANT.  L does not appear: every A_j is already joint. *)
(* ----------------------------------------------------------------- *)
Definition M4fin (t : R) : R :=
  A4 + 4 * (A3 * Tt t) + 6 * (A2 * (Tt t * Tt t))
  + 4 * (A1 * (Tt t * (Tt t * Tt t)))
  + A0 * (Tt t * (Tt t * (Tt t * Tt t))).

Theorem G4_bdd : forall t L, BddOn (G4 t) 0 L (M4fin t).
Proof.
  intros t L x Hx. unfold G4, M4fin.
  pose proof (PG4_bdd L x Hx) as P4. pose proof (PG3_bdd L x Hx) as P3.
  pose proof (PG2_bdd L x Hx) as P2. pose proof (PG1_bdd L x Hx) as P1.
  pose proof (PG0_bdd L x Hx) as P0.
  pose proof (Ct_bdd t L x Hx) as C0. pose proof (Ct'_bdd t L x Hx) as C1.
  pose proof (Ct''_bdd t L x Hx) as C2. pose proof (Ct3_bdd t L x Hx) as C3.
  pose proof (Ct4_bdd t L x Hx) as C4.
  unfold Tt in *.
  apply abs5.
  - replace A4 with (A4 * 1) by ring. apply abs_prod_le; assumption.
  - apply abs_scal_le; [ lra | apply abs_prod_le; assumption ].
  - apply abs_scal_le; [ lra | apply abs_prod_le; assumption ].
  - apply abs_scal_le; [ lra | apply abs_prod_le; assumption ].
  - apply abs_prod_le; assumption.
Qed.

Lemma M4fin_nonneg : forall t, 0 <= M4fin t.
Proof.
  intro t. unfold M4fin, A0, A1, A2, A3, A4.
  destruct B_nonneg as [N0 [N1 [N2 [N3 N4]]]].
  assert (HT : 0 <= Tt t) by (unfold Tt; pose proof (Rabs_pos t); lra).
  assert (Q1 : 0 <= Tt t * Tt t) by (apply Rmult_le_pos; lra).
  assert (Q2 : 0 <= Tt t * (Tt t * Tt t)) by (apply Rmult_le_pos; lra).
  assert (Q3 : 0 <= Tt t * (Tt t * (Tt t * Tt t))) by (apply Rmult_le_pos; lra).
  assert (S1 : 0 <= B1 + / 4 * B0) by lra.
  assert (S2 : 0 <= B2 + / 2 * B1 + / 16 * B0) by lra.
  assert (S3 : 0 <= B3 + 3 / 4 * B2 + 3 / 16 * B1 + / 64 * B0) by lra.
  assert (S4 : 0 <= B4 + B3 + 3 / 8 * B2 + / 16 * B1 + / 256 * B0) by lra.
  assert (P1 : 0 <= (B3 + 3 / 4 * B2 + 3 / 16 * B1 + / 64 * B0) * Tt t)
    by (apply Rmult_le_pos; lra).
  assert (P2 : 0 <= (B2 + / 2 * B1 + / 16 * B0) * (Tt t * Tt t))
    by (apply Rmult_le_pos; lra).
  assert (P3 : 0 <= (B1 + / 4 * B0) * (Tt t * (Tt t * Tt t)))
    by (apply Rmult_le_pos; lra).
  assert (P4 : 0 <= B0 * (Tt t * (Tt t * (Tt t * Tt t))))
    by (apply Rmult_le_pos; lra).
  lra.
Qed.

(* the Lipschitz constant for the THIRD derivative comes from a genuine *)
(* bound on the FOURTH -- available only because PsiXDeriv3 gets order  *)
(* 4 out of the same moment recursion, at no extra cost.                *)
Theorem d3gint_lip : forall t L, LipOn (G3 t) 0 L (M4fin t).
Proof.
  intros t L. apply (lip_of_deriv (G3 t) (G4 t) 0 L).
  - intros y Hy. apply gint_deriv_4. apply Hy.
  - apply G4_bdd.
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  SIMPSON, DISCHARGED for the integrand                          *)
(* ----------------------------------------------------------------- *)
Theorem gint_simpson : forall t L c r
  (prf : Riemann_integrable (gint t) (c - r) (c + r)),
  0 <= r -> 0 <= c - r -> c + r <= L ->
  Rabs (RiemannInt prf
        - r / 3 * (gint t (c - r) + 4 * gint t c + gint t (c + r)))
  <= 2 * M4fin t * r ^ 5 / 45.
Proof.
  intros t L c r prf Hr Hlo Hhi.
  apply (simpson_single (gint t) (G1 t) (G2 t) (G3 t) c (M4fin t) r prf).
  - exact Hr.
  - apply M4fin_nonneg.
  - intros y Hy. apply gint_deriv_1. lra.
  - intros y Hy. apply gint_deriv_2. lra.
  - intros y Hy. apply gint_deriv_3. lra.
  - intros y z Hy Hz. apply (d3gint_lip t L); split; lra.
Qed.

Print Assumptions PG4_bdd.
Print Assumptions gint_deriv_4.
Print Assumptions G4_bdd.
Print Assumptions d3gint_lip.
Print Assumptions gint_simpson.
