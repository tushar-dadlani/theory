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
        GammaReal GammaFunction GammaContinuity ImproperCv0 ImproperCv1 CImproperIntegral
        CImpZero GammaNearC.
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

Lemma continuity_pt_ext : forall f g t,
  (forall x, f x = g x) -> continuity_pt f t -> continuity_pt g t.
Proof.
  intros f g t H Hf; assert (Heq : f = g) by (apply functional_extensionality; exact H);
    subst; exact Hf.
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

(* --- Part 3: the total wrapper, CImp0 assembly, and gnearC_entire --- *)

(* proof-irrelevance of gnearC (both are the CImp0 value of gnkC z) *)
Lemma gnearC_pirr : forall z (H1 H2 : 0 < Re z), gnearC z H1 = gnearC z H2.
Proof.
  intros z H1 H2.
  destruct (gnearC_spec z H1) as [HRe1 HIm1]; destruct (gnearC_spec z H2) as [HRe2 HIm2].
  apply Ceq.
  - apply (improper_unique0 (fun u => Re (gnkC z u)) (Hre_gnkC z) (fun u => Re (gnkC z u))
             (Hre_gnkC z) (Re (gnearC z H1)) (Re (gnearC z H2)));
      [ intros; reflexivity | exact HRe1 | exact HRe2 ].
  - apply (improper_unique0 (fun u => Im (gnkC z u)) (Him_gnkC z) (fun u => Im (gnkC z u))
             (Him_gnkC z) (Im (gnearC z H1)) (Im (gnearC z H2)));
      [ intros; reflexivity | exact HIm1 | exact HIm2 ].
Qed.

(* the TOTAL wrapper *)
Definition gnearCt (z : C) : C :=
  match Rlt_dec 0 (Re z) with left Hz => gnearC z Hz | right _ => C0 end.

Lemma gnearCt_val : forall z (Hz : 0 < Re z), gnearCt z = gnearC z Hz.
Proof.
  intros z Hz; unfold gnearCt; destruct (Rlt_dec 0 (Re z)) as [Hz' | Hn];
    [ exact (gnearC_pirr z Hz' Hz) | exfalso; lra ].
Qed.

(* --- Ccont0: both components continuous on (0,∞) --- *)
Definition Ccont0 (k : R -> C) : Prop :=
  (forall t, 0 < t -> continuity_pt (fun u => Re (k u)) t) /\
  (forall t, 0 < t -> continuity_pt (fun u => Im (k u)) t).

Lemma Ccont0_const : forall c, Ccont0 (fun _ => c).
Proof. intro c; split; intros t _; apply continuity_pt_const; red; intros; reflexivity. Qed.

Lemma Ccont0_minus : forall a b, Ccont0 a -> Ccont0 b -> Ccont0 (fun u => Cminus (a u) (b u)).
Proof.
  intros a b [Har Hai] [Hbr Hbi]; split; intros t Ht.
  - apply (continuity_pt_ext (fun u => Re (a u) - Re (b u)));
      [ intro u; unfold Cminus, Cadd, Copp; cbn; ring | apply continuity_pt_minus; auto ].
  - apply (continuity_pt_ext (fun u => Im (a u) - Im (b u)));
      [ intro u; unfold Cminus, Cadd, Copp; cbn; ring | apply continuity_pt_minus; auto ].
Qed.

Lemma Ccont0_mul : forall a b, Ccont0 a -> Ccont0 b -> Ccont0 (fun u => Cmul (a u) (b u)).
Proof.
  intros a b [Har Hai] [Hbr Hbi]; split; intros t Ht.
  - apply (continuity_pt_ext (fun u => Re (a u) * Re (b u) - Im (a u) * Im (b u)));
      [ intro u; unfold Cmul; cbn; ring
      | apply continuity_pt_minus; apply continuity_pt_mult; auto ].
  - apply (continuity_pt_ext (fun u => Re (a u) * Im (b u) + Im (a u) * Re (b u)));
      [ intro u; unfold Cmul; cbn; ring
      | apply continuity_pt_plus; apply continuity_pt_mult; auto ].
Qed.

Lemma Ccont0_gnkC : forall z, Ccont0 (gnkC z).
Proof. intro z; split; [ apply cont_Re_gnkC | apply cont_Im_gnkC ]. Qed.
Lemma Ccont0_dgnkC : forall z, Ccont0 (dgnkC z).
Proof. intro z; split; [ apply cont_Re_dgnkC | apply cont_Im_dgnkC ]. Qed.

Lemma Ccont0_remGnC : forall z h, Ccont0 (remGnC z h).
Proof.
  intros z h; unfold remGnC; apply Ccont0_minus.
  - apply Ccont0_minus; apply Ccont0_gnkC.
  - apply Ccont0_mul; [ apply Ccont0_const | apply Ccont0_dgnkC ].
Qed.

Lemma cont_Cmod_remGnC : forall z h t, 0 < t -> continuity_pt (fun u => Cmod (remGnC z h u)) t.
Proof.
  intros z h t Ht.
  assert (Hcn : continuity_pt (fun u => Cnorm2 (remGnC z h u)) t).
  { apply (continuity_pt_ext (fun u => Re (remGnC z h u) * Re (remGnC z h u)
                                     + Im (remGnC z h u) * Im (remGnC z h u)));
      [ intro w; reflexivity | ].
    apply continuity_pt_plus; apply continuity_pt_mult;
      first [ apply (proj1 (Ccont0_remGnC z h)); exact Ht
            | apply (proj2 (Ccont0_remGnC z h)); exact Ht ]. }
  apply (continuity_pt_comp (fun u => Cnorm2 (remGnC z h u)) sqrt t);
    [ exact Hcn | apply continuity_pt_sqrt; apply Cnorm2_nonneg ].
Qed.

(* the CImp0 of remGnC identifies the increment *)
Lemma remGnC_CImp0 : forall z h (Hz : 0 < Re z) (Hzh : 0 < Re (Cadd z h)),
  CImp0 (remGnC z h) (cont_pos_RI _ (proj1 (Ccont0_remGnC z h)))
    (cont_pos_RI _ (proj2 (Ccont0_remGnC z h)))
    (Cminus (Cminus (gnearC (Cadd z h) Hzh) (gnearC z Hz)) (Cmul h (dgnearC z Hz))).
Proof.
  intros z h Hz Hzh; unfold remGnC.
  apply (CImp0_minus
           (fun u => Cminus (gnkC (Cadd z h) u) (gnkC z u)) (fun u => Cmul h (dgnkC z u))
           (cont_pos_RI _ (proj1 (Ccont0_minus _ _ (Ccont0_gnkC (Cadd z h)) (Ccont0_gnkC z))))
           (cont_pos_RI _ (proj2 (Ccont0_minus _ _ (Ccont0_gnkC (Cadd z h)) (Ccont0_gnkC z))))
           (cont_pos_RI _ (proj1 (Ccont0_mul _ _ (Ccont0_const h) (Ccont0_dgnkC z))))
           (cont_pos_RI _ (proj2 (Ccont0_mul _ _ (Ccont0_const h) (Ccont0_dgnkC z))))
           (cont_pos_RI _ (proj1 (Ccont0_remGnC z h)))
           (cont_pos_RI _ (proj2 (Ccont0_remGnC z h)))
           (Cminus (gnearC (Cadd z h) Hzh) (gnearC z Hz)) (Cmul h (dgnearC z Hz))).
  - apply (CImp0_minus (gnkC (Cadd z h)) (gnkC z)
             (Hre_gnkC (Cadd z h)) (Him_gnkC (Cadd z h)) (Hre_gnkC z) (Him_gnkC z)
             (cont_pos_RI _ (proj1 (Ccont0_minus _ _ (Ccont0_gnkC (Cadd z h)) (Ccont0_gnkC z))))
             (cont_pos_RI _ (proj2 (Ccont0_minus _ _ (Ccont0_gnkC (Cadd z h)) (Ccont0_gnkC z))))
             (gnearC (Cadd z h) Hzh) (gnearC z Hz));
      [ apply (gnearC_spec (Cadd z h) Hzh) | apply (gnearC_spec z Hz) ].
  - apply (CImp0_cscal h (dgnkC z) (Hre_dgnkC z) (Him_dgnkC z)
             (cont_pos_RI _ (proj1 (Ccont0_mul _ _ (Ccont0_const h) (Ccont0_dgnkC z))))
             (cont_pos_RI _ (proj2 (Ccont0_mul _ _ (Ccont0_const h) (Ccont0_dgnkC z))))
             (dgnearC z Hz));
      apply (dgnearC_spec z Hz).
Qed.

(* convergence of ∫ Cmod(remGnC), bounded by |h|^2·3·L *)
Lemma Cmod_remGnC_conv : forall z h (Hz : 0 < Re z), Cmod h <= Re z / 2 ->
  { J | ImproperCv0 (fun u => Cmod (remGnC z h u)) (cont_pos_RI _ (cont_Cmod_remGnC z h)) J }.
Proof.
  intros z h Hz Hh; assert (Hz2 : 0 < Re z / 2) by lra.
  apply improper_bounded_cv0.
  - intros x _ _; apply Cmod_nonneg.
  - exists (Cmod h ^ 2 * 3 * proj1_sig (ln2_gnk_conv (Re z / 2) Hz2)); intros A HA HA1.
    apply Rle_trans with
      (rint01 (fun u => Cmod h ^ 2 * 3 * ((ln u) ^ 2 * gnk (Re z / 2) 1 u))
         (fun x y Hx Hxy => RI_scal _ (Cmod h ^ 2 * 3) x y (cont_pos_RI _ (cont_ln2_gnk (Re z / 2)) x y Hx Hxy)) A).
    + rewrite (rint01_val (fun u => Cmod (remGnC z h u)) _ A HA HA1),
        (rint01_val (fun u => Cmod h ^ 2 * 3 * ((ln u) ^ 2 * gnk (Re z / 2) 1 u)) _ A HA HA1).
      apply RiemannInt_P19; [ exact HA1 | intros x Hx; apply Cmod_remGnC_le; lra ].
    + rewrite (rint01_val (fun u => Cmod h ^ 2 * 3 * ((ln u) ^ 2 * gnk (Re z / 2) 1 u)) _ A HA HA1).
      rewrite (RiemannInt_scal01 (fun u => (ln u) ^ 2 * gnk (Re z / 2) 1 u) (Cmod h ^ 2 * 3) A
                 (cont_pos_RI _ (cont_ln2_gnk (Re z / 2)) A 1 HA HA1) _ HA1).
      apply Rmult_le_compat_l.
      * apply Rmult_le_pos; [ apply pow_le; apply Cmod_nonneg | lra ].
      * rewrite <- (rint01_val (fun u => (ln u) ^ 2 * gnk (Re z / 2) 1 u)
                     (cont_pos_RI _ (cont_ln2_gnk (Re z / 2))) A HA HA1).
        apply (rint01_le_improper (fun u => (ln u) ^ 2 * gnk (Re z / 2) 1 u)
                 (cont_pos_RI _ (cont_ln2_gnk (Re z / 2))) _
                 (proj2_sig (ln2_gnk_conv (Re z / 2) Hz2)));
          [ intros x Hx Hx1; apply Rmult_le_pos; [ apply ln2_nonneg | apply gnk_nonneg ]
          | exact HA | exact HA1 ].
Qed.

Lemma gnearC_deriv_bound : forall z h (Hz : 0 < Re z) (Hzh : 0 < Re (Cadd z h)),
  Cmod h <= Re z / 2 ->
  Cmod (Cminus (Cminus (gnearC (Cadd z h) Hzh) (gnearC z Hz)) (Cmul (dgnearC z Hz) h))
  <= Cmod h ^ 2 * 3 * proj1_sig (ln2_gnk_conv (Re z / 2) (Rlt_gt 0 (Re z / 2) ltac:(lra))).
Proof.
  intros z h Hz Hzh Hh.
  replace (Cmul (dgnearC z Hz) h) with (Cmul h (dgnearC z Hz)) by ring.
  destruct (Cmod_remGnC_conv z h Hz Hh) as [J HJ].
  apply Rle_trans with J.
  - apply (CImp0_triangle _ _ _ _ _ _ (remGnC_CImp0 z h Hz Hzh) HJ).
  - apply (improper_mono0 (fun u => Cmod (remGnC z h u)) (cont_pos_RI _ (cont_Cmod_remGnC z h))
             (fun u => Cmod h ^ 2 * 3 * ((ln u) ^ 2 * gnk (Re z / 2) 1 u))
             (fun x y Hx Hxy => RI_scal _ (Cmod h ^ 2 * 3) x y (cont_pos_RI _ (cont_ln2_gnk (Re z / 2)) x y Hx Hxy))
             J (Cmod h ^ 2 * 3 * proj1_sig (ln2_gnk_conv (Re z / 2) (Rlt_gt 0 (Re z / 2) ltac:(lra))))
             HJ).
    + (* the dominator's ImproperCv0 value = |h|^2·3·L *)
      apply (improper_scal0 (fun u => (ln u) ^ 2 * gnk (Re z / 2) 1 u) (Cmod h ^ 2 * 3)
               (cont_pos_RI _ (cont_ln2_gnk (Re z / 2)))
               (fun x y Hx Hxy => RI_scal _ (Cmod h ^ 2 * 3) x y (cont_pos_RI _ (cont_ln2_gnk (Re z / 2)) x y Hx Hxy))
               (proj1_sig (ln2_gnk_conv (Re z / 2) (Rlt_gt 0 (Re z / 2) ltac:(lra)))));
        exact (proj2_sig (ln2_gnk_conv (Re z / 2) (Rlt_gt 0 (Re z / 2) ltac:(lra)))).
    + intros x Hx Hx1; apply Cmod_remGnC_le; lra.
Qed.

Theorem gnearC_entire : forall z (Hz : 0 < Re z), is_Cderiv gnearCt z (dgnearC z Hz).
Proof.
  intros z Hz eps Heps.
  set (L := proj1_sig (ln2_gnk_conv (Re z / 2) (Rlt_gt 0 (Re z / 2) ltac:(lra)))).
  assert (HL : 0 <= L).
  { unfold L; destruct (ln2_gnk_conv (Re z / 2) _) as [L0 HL0]; simpl.
    apply (improper_nonneg0 (fun u => (ln u) ^ 2 * gnk (Re z / 2) 1 u)
             (cont_pos_RI _ (cont_ln2_gnk (Re z / 2))) L0);
      [ intros x Hx Hx1; apply Rmult_le_pos; [ apply ln2_nonneg | apply gnk_nonneg ] | exact HL0 ]. }
  set (K := 3 * L).
  assert (HK : 0 <= K) by (unfold K; lra).
  assert (Hd : 0 < eps / (K + 1)) by (apply Rdiv_lt_0_compat; lra).
  exists (Rmin (Re z / 2) (Rmin 1 (eps / (K + 1)))); split.
  - repeat apply Rmin_glb_lt; lra.
  - intros h Hlt.
    assert (Hgate : Cmod h <= Re z / 2)
      by (apply Rlt_le; apply Rlt_le_trans with (Rmin (Re z / 2) (Rmin 1 (eps / (K + 1)))); [ exact Hlt | apply Rmin_l ]).
    assert (Hh1 : Cmod h <= 1)
      by (apply Rlt_le; apply Rlt_le_trans with (Rmin (Re z / 2) (Rmin 1 (eps / (K + 1))));
          [ exact Hlt | eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ] ]).
    assert (Hlt2 : Cmod h < eps / (K + 1))
      by (apply Rlt_le_trans with (Rmin (Re z / 2) (Rmin 1 (eps / (K + 1))));
          [ exact Hlt | eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ] ]).
    assert (Hzh : 0 < Re (Cadd z h)).
    { assert (HR : Re (Cadd z h) = Re z + Re h) by (unfold Cadd; cbn; ring).
      pose proof (Cmod_Re h) as HRh; pose proof (Rle_abs (Re h)) as U;
        pose proof (Rle_abs (- Re h)) as W; rewrite Rabs_Ropp in W; rewrite HR; lra. }
    rewrite (gnearCt_val (Cadd z h) Hzh), (gnearCt_val z Hz).
    apply Rle_trans with (Cmod h ^ 2 * 3 * L).
    + exact (gnearC_deriv_bound z h Hz Hzh Hgate).
    + assert (HcK : Cmod h * (K + 1) < eps).
      { apply Rlt_le_trans with (eps / (K + 1) * (K + 1));
          [ apply Rmult_lt_compat_r; [ lra | exact Hlt2 ] | right; field; lra ]. }
      pose proof (Cmod_nonneg h) as Hcm; unfold K in HcK; nra.
Qed.

Print Assumptions Cmod_remGnC_le.
Print Assumptions gnearC_entire.

(* ================================================================= *)
(*  END GammaNearCHolo.v (gnearC is holomorphic on Re z > 0).          *)
(* ================================================================= *)
