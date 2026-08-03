(* ================================================================= *)
(*  GammaNearCHolo.v  —  the CRUX: gnearC is holomorphic on Re z > 0.   *)
(*  Replicates ThetaTailEntire's TC_entire on (0,1], with the three     *)
(*  departures forced by raw u<=1 (ln u<=0):  Rabs / even powers,        *)
(*  the exp(|w|)=u^{-|h|} blow-up (|h|<=Re z/2 gate + gnk(Re z/2) shift), *)
(*  and a z-dependent del.  Part 1: near-0 dominators + dgnkC/dgnearC.    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia FunctionalExtensionality.
Require Import ComplexField Cmodulus CexpFull CexpRemainder CPowBase Holomorphic
        GammaReal GammaFunction ImproperCv0 ImproperCv1 CImproperIntegral CImpZero GammaNearC.
Open Scope R_scope.

(* --- the crux calculus (validated) --- *)
Lemma ln2_Rpower_bound : forall d u, 0 < d -> 0 < u -> u <= 1 ->
  (ln u) ^ 2 <= 4 / d ^ 2 * Rpower u (- d).
Proof.
  intros d u Hd Hu Hu1.
  assert (Hlnu : ln u <= 0).
  { destruct (Rle_lt_or_eq_dec u 1 Hu1) as [Hlt | Heq].
    - rewrite <- ln_1; left; apply ln_increasing; lra.
    - subst; rewrite ln_1; lra. }
  set (x := d * (- ln u)).
  assert (Hx : 0 <= x) by (unfold x; apply Rmult_le_pos; lra).
  pose proof (exp_lb2 1 x Hx) as Hlb.
  replace (INR (S 1) ^ (S 1)) with 4 in Hlb by (simpl; ring).
  replace (x ^ (S 1)) with (x ^ 2) in Hlb by (simpl; ring).
  assert (Hexp : exp x = Rpower u (- d)) by (unfold x, Rpower; f_equal; ring).
  rewrite Hexp in Hlb.
  assert (Hx2 : x ^ 2 = d ^ 2 * (ln u) ^ 2) by (unfold x; ring).
  rewrite Hx2 in Hlb.
  apply Rmult_le_reg_l with (d ^ 2 / 4).
  { apply Rdiv_lt_0_compat; [ nra | lra ]. }
  replace (d ^ 2 / 4 * (4 / d ^ 2 * Rpower u (- d))) with (Rpower u (- d)) by (field; nra).
  replace (d ^ 2 / 4 * (ln u) ^ 2) with (d ^ 2 * (ln u) ^ 2 / 4) by field.
  exact Hlb.
Qed.

Lemma ln2_gnk_le : forall s u, 0 < s -> 0 < u -> u <= 1 ->
  (ln u) ^ 2 * gnk s 1 u <= 16 / s ^ 2 * gnk (s / 2) 1 u.
Proof.
  intros s u Hs Hu Hu1.
  pose proof (ln2_Rpower_bound (s / 2) u ltac:(lra) Hu Hu1) as Hb.
  assert (Hg : 0 <= gnk s 1 u) by apply gnk_nonneg.
  apply Rle_trans with (4 / (s / 2) ^ 2 * Rpower u (- (s / 2)) * gnk s 1 u).
  - apply Rmult_le_compat_r; [ exact Hg | exact Hb ].
  - unfold gnk.
    replace (4 / (s / 2) ^ 2) with (16 / s ^ 2) by (field; lra).
    replace (16 / s ^ 2 * Rpower u (- (s / 2)) * (Rpower u (s - 1) * exp (- (1 * u))))
      with (16 / s ^ 2 * (Rpower u (- (s / 2)) * Rpower u (s - 1)) * exp (- (1 * u))) by ring.
    rewrite <- Rpower_plus.
    replace (- (s / 2) + (s - 1)) with (s / 2 - 1) by field.
    apply Req_le; ring.
Qed.

(* (ln u)^2 >= 0 *)
Lemma ln2_nonneg : forall u, 0 <= (ln u) ^ 2.
Proof. intro u; replace ((ln u) ^ 2) with (Rsqr (ln u)) by (unfold Rsqr; ring); apply Rle_0_sqr. Qed.

Lemma abs_le_sq1 : forall y, Rabs y <= y ^ 2 + 1.
Proof.
  intro y; pose proof (Rle_0_sqr (Rabs y - 1)) as H; unfold Rsqr in H.
  pose proof (Rsqr_abs y) as Ha; unfold Rsqr in Ha.
  pose proof (Rabs_pos y).
  replace (y ^ 2) with (y * y) by ring; nra.
Qed.

(* --- continuity on (0,∞) of the near-0 dominator integrands --- *)
Lemma cont_ln : forall t, 0 < t -> continuity_pt ln t.
Proof.
  intros t Ht; apply derivable_continuous_pt; exists (/ t); apply derivable_pt_lim_ln; exact Ht.
Qed.

Lemma cont_ln2_gnk : forall s t, 0 < t -> continuity_pt (fun u => (ln u) ^ 2 * gnk s 1 u) t.
Proof.
  intros s t Ht; apply continuity_pt_mult; [ | apply cont_gnk; exact Ht ].
  assert (Heq : (fun u => (ln u) ^ 2) = (fun u => ln u * ln u))
    by (apply functional_extensionality; intro u; ring).
  rewrite Heq; apply continuity_pt_mult; apply cont_ln; exact Ht.
Qed.

Lemma cont_absln_gnk : forall s t, 0 < t -> continuity_pt (fun u => Rabs (ln u) * gnk s 1 u) t.
Proof.
  intros s t Ht; apply continuity_pt_mult; [ | apply cont_gnk; exact Ht ].
  apply (continuity_pt_comp ln Rabs); [ apply cont_ln; exact Ht | apply Rcontinuity_abs ].
Qed.

(* --- the two near-0 dominator convergences (via abs_conv_component0) --- *)
Lemma ln2_gnk_conv : forall s (Hs : 0 < s),
  { I | ImproperCv0 (fun u => (ln u) ^ 2 * gnk s 1 u) (cont_pos_RI _ (cont_ln2_gnk s)) I }.
Proof.
  intros s Hs; assert (Hs2 : 0 < s / 2) by lra.
  apply (abs_conv_component0 (fun u => (ln u) ^ 2 * gnk s 1 u)
           (fun u => 16 / s ^ 2 * gnk (s / 2) 1 u)
           (fun x y Hx Hxy => RI_scal (gnk (s / 2) 1) (16 / s ^ 2) x y (Hf_near (s / 2) 1 x y Hx Hxy))
           (16 / s ^ 2 * gnear (s / 2) 1 Hs2 Rlt_0_1)
           (cont_pos_RI _ (cont_ln2_gnk s))).
  - intros x Hx Hx1; rewrite Rabs_right
      by (apply Rle_ge; apply Rmult_le_pos; [ apply ln2_nonneg | apply gnk_nonneg ]).
    apply ln2_gnk_le; assumption.
  - apply (improper_scal0 (gnk (s / 2) 1) (16 / s ^ 2) (Hf_near (s / 2) 1)
             (fun x y Hx Hxy => RI_scal (gnk (s / 2) 1) (16 / s ^ 2) x y (Hf_near (s / 2) 1 x y Hx Hxy))
             (gnear (s / 2) 1 Hs2 Rlt_0_1));
      exact (proj2_sig (gnear_sig (s / 2) 1 Hs2 Rlt_0_1)).
Qed.

Lemma abs_ln_gnk_conv : forall s (Hs : 0 < s),
  { I | ImproperCv0 (fun u => Rabs (ln u) * gnk s 1 u) (cont_pos_RI _ (cont_absln_gnk s)) I }.
Proof.
  intros s Hs.
  destruct (ln2_gnk_conv s Hs) as [I2 HI2].
  apply (abs_conv_component0 (fun u => Rabs (ln u) * gnk s 1 u)
           (fun u => (ln u) ^ 2 * gnk s 1 u + 1 * gnk s 1 u)
           (fun x y Hx Hxy => RiemannInt_P10 1 (cont_pos_RI _ (cont_ln2_gnk s) x y Hx Hxy)
                                 (Hf_near s 1 x y Hx Hxy))
           (I2 + 1 * gnear s 1 Hs Rlt_0_1)
           (cont_pos_RI _ (cont_absln_gnk s))).
  - intros x Hx Hx1; rewrite Rabs_right
      by (apply Rle_ge; apply Rmult_le_pos; [ apply Rabs_pos | apply gnk_nonneg ]).
    apply Rle_trans with (((ln x) ^ 2 + 1) * gnk s 1 x).
    + apply Rmult_le_compat_r; [ apply gnk_nonneg | apply abs_le_sq1 ].
    + apply Req_le; ring.
  - apply (improper_linear0 (fun u => (ln u) ^ 2 * gnk s 1 u) (gnk s 1) 1
             (cont_pos_RI _ (cont_ln2_gnk s)) (Hf_near s 1)
             (fun x y Hx Hxy => RiemannInt_P10 1 (cont_pos_RI _ (cont_ln2_gnk s) x y Hx Hxy)
                                   (Hf_near s 1 x y Hx Hxy))
             I2 (gnear s 1 Hs Rlt_0_1) HI2 (proj2_sig (gnear_sig s 1 Hs Rlt_0_1))).
Qed.

(* --- the derivative kernel dgnkC = ln u · gnkC --- *)
Definition dgnkC (z : C) (u : R) : C := Cmul (RtoC (ln u)) (gnkC z u).

Lemma Cmod_dgnkC : forall z u, Cmod (dgnkC z u) = Rabs (ln u) * gnk (Re z) 1 u.
Proof. intros z u; unfold dgnkC; rewrite Cmod_mul, Cmod_RtoC, Cmod_gnkC; reflexivity. Qed.

Lemma cont_Re_dgnkC : forall z t, 0 < t -> continuity_pt (fun u => Re (dgnkC z u)) t.
Proof.
  intros z t Ht.
  assert (Heq : (fun u => Re (dgnkC z u)) = (fun u => ln u * Re (gnkC z u)))
    by (apply functional_extensionality; intro u; unfold dgnkC, Cmul, RtoC; cbn; ring).
  rewrite Heq; apply continuity_pt_mult; [ apply cont_ln; exact Ht | apply cont_Re_gnkC; exact Ht ].
Qed.

Lemma cont_Im_dgnkC : forall z t, 0 < t -> continuity_pt (fun u => Im (dgnkC z u)) t.
Proof.
  intros z t Ht.
  assert (Heq : (fun u => Im (dgnkC z u)) = (fun u => ln u * Im (gnkC z u)))
    by (apply functional_extensionality; intro u; unfold dgnkC, Cmul, RtoC; cbn; ring).
  rewrite Heq; apply continuity_pt_mult; [ apply cont_ln; exact Ht | apply cont_Im_gnkC; exact Ht ].
Qed.

Definition Hre_dgnkC (z : C) := cont_pos_RI (fun u => Re (dgnkC z u)) (cont_Re_dgnkC z).
Definition Him_dgnkC (z : C) := cont_pos_RI (fun u => Im (dgnkC z u)) (cont_Im_dgnkC z).

Definition dgnearC_sig (z : C) (Hz : 0 < Re z) :
  { I : C | CImp0 (dgnkC z) (Hre_dgnkC z) (Him_dgnkC z) I } :=
  CImp0_abs (dgnkC z) (fun u => Rabs (ln u) * gnk (Re z) 1 u)
    (cont_pos_RI _ (cont_absln_gnk (Re z))) (proj1_sig (abs_ln_gnk_conv (Re z) Hz))
    (Hre_dgnkC z) (Him_dgnkC z)
    (fun x _ _ => Req_le _ _ (Cmod_dgnkC z x)) (proj2_sig (abs_ln_gnk_conv (Re z) Hz)).

Definition dgnearC (z : C) (Hz : 0 < Re z) : C := proj1_sig (dgnearC_sig z Hz).

Lemma dgnearC_spec : forall z (Hz : 0 < Re z),
  CImp0 (dgnkC z) (Hre_dgnkC z) (Him_dgnkC z) (dgnearC z Hz).
Proof. intros z Hz; exact (proj2_sig (dgnearC_sig z Hz)). Qed.

(* --- Part 2: shift, remainder, and the crux modulus bound --- *)

Lemma exp_le' : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b H; destruct (Rle_lt_or_eq_dec a b H) as [Hlt | Heq];
    [ left; apply exp_increasing; exact Hlt | subst; apply Rle_refl ].
Qed.

(* Rpower u is ANTItone in the exponent for 0 < u <= 1 (ln u <= 0). *)
Lemma Rpower_antitone : forall u a b, 0 < u -> u <= 1 -> a <= b -> Rpower u b <= Rpower u a.
Proof.
  intros u a b Hu Hu1 Hab.
  assert (Hln : ln u <= 0).
  { destruct (Rle_lt_or_eq_dec u 1 Hu1) as [Hlt | Heq];
      [ rewrite <- ln_1; left; apply ln_increasing; lra | subst; rewrite ln_1; lra ]. }
  unfold Rpower; apply exp_le'.
  rewrite (Rmult_comm b (ln u)), (Rmult_comm a (ln u)).
  apply Rmult_le_compat_neg_l; [ exact Hln | exact Hab ].
Qed.

Definition gnshift (h : C) (u : R) : C := Cmul h (RtoC (ln u)).

Lemma Cmod_gnshift : forall h u, Cmod (gnshift h u) = Cmod h * Rabs (ln u).
Proof. intros h u; unfold gnshift; rewrite Cmod_mul, Cmod_RtoC; reflexivity. Qed.

Lemma gnkC_shift : forall z h u, gnkC (Cadd z h) u = Cmul (gnkC z u) (Cexpf (gnshift h u)).
Proof.
  intros z h u; unfold gnkC, gnshift.
  assert (HE : Cminus (Cadd z h) C1 = Cadd (Cminus z C1) h) by ring.
  rewrite HE, Cpw_split. unfold Cpw. ring.
Qed.

Definition remGnC (z h : C) (u : R) : C :=
  Cminus (Cminus (gnkC (Cadd z h) u) (gnkC z u)) (Cmul h (dgnkC z u)).

Lemma remGnC_eq : forall z h u,
  remGnC z h u = Cmul (gnkC z u) (Cminus (Cminus (Cexpf (gnshift h u)) C1) (gnshift h u)).
Proof.
  intros z h u; unfold remGnC, dgnkC.
  rewrite gnkC_shift.
  assert (Hlin : Cmul h (Cmul (RtoC (ln u)) (gnkC z u)) = Cmul (gnkC z u) (gnshift h u))
    by (unfold gnshift; ring).
  rewrite Hlin. ring.
Qed.

Lemma Cmod_remGnC_le : forall z h u, 0 < u -> u <= 1 -> Cmod h <= Re z / 2 ->
  Cmod (remGnC z h u) <= Cmod h ^ 2 * 3 * ((ln u) ^ 2 * gnk (Re z / 2) 1 u).
Proof.
  intros z h u Hu Hu1 Hh.
  rewrite remGnC_eq, Cmod_mul, Cmod_gnkC.
  assert (Hln : ln u <= 0).
  { destruct (Rle_lt_or_eq_dec u 1 Hu1) as [Hlt | Heq];
      [ rewrite <- ln_1; left; apply ln_increasing; lra | subst; rewrite ln_1; lra ]. }
  assert (HexpEq : exp (Cmod h * Rabs (ln u)) = Rpower u (- Cmod h))
    by (rewrite (Rabs_left1 (ln u)) by exact Hln; unfold Rpower; f_equal; ring).
  assert (Hexple : Rpower u (- Cmod h) <= Rpower u (- (Re z / 2)))
    by (apply Rpower_antitone; [ exact Hu | exact Hu1 | lra ]).
  assert (Hfold : gnk (Re z) 1 u * Rpower u (- (Re z / 2)) = gnk (Re z / 2) 1 u).
  { unfold gnk.
    rewrite Rmult_assoc, (Rmult_comm (exp (- (1 * u))) (Rpower u (- (Re z / 2)))).
    rewrite <- Rmult_assoc, <- Rpower_plus.
    replace (Re z - 1 + - (Re z / 2)) with (Re z / 2 - 1) by field; reflexivity. }
  assert (Hcoef : 0 <= 3 * (Cmod h * Rabs (ln u)) ^ 2).
  { apply Rmult_le_pos; [ lra | apply pow_le; apply Rmult_le_pos;
      [ apply Cmod_nonneg | apply Rabs_pos ] ]. }
  apply Rle_trans with (gnk (Re z) 1 u * (3 * (Cmod (gnshift h u)) ^ 2 * exp (Cmod (gnshift h u)))).
  - apply Rmult_le_compat_l; [ apply gnk_nonneg | apply Cexpf_remainder ].
  - rewrite Cmod_gnshift, HexpEq.
    apply Rle_trans with
      (gnk (Re z) 1 u * (3 * (Cmod h * Rabs (ln u)) ^ 2 * Rpower u (- (Re z / 2)))).
    + apply Rmult_le_compat_l; [ apply gnk_nonneg | ].
      apply Rmult_le_compat_l; [ exact Hcoef | exact Hexple ].
    + right. rewrite <- Hfold.
      replace ((Cmod h * Rabs (ln u)) ^ 2) with (Cmod h ^ 2 * (ln u) ^ 2)
        by (rewrite Rpow_mult_distr; f_equal;
            pose proof (Rsqr_abs (ln u)); unfold Rsqr in *; nra).
      ring.
Qed.

Print Assumptions ln2_gnk_conv.
Print Assumptions dgnearC_spec.
Print Assumptions Cmod_remGnC_le.

(* ================================================================= *)
(*  END GammaNearCHolo.v Parts 1-2 (dominators, kernel, remainder).    *)
(* ================================================================= *)
