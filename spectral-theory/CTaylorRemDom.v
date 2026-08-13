(* ================================================================= *)
(*  CTaylorRemDom.v  (identity-theorem plan, DOMAIN-RESTRICTED B4)      *)
(*                                                                    *)
(*  taylor_center_zero for an f holomorphic only on the disk |z|<R+1   *)
(*  and pointwise-continuous everywhere (NOT entire).  Identical to     *)
(*  CTaylorRem.taylor_center_zero except the single B1 call swaps       *)
(*  cauchy_interior -> CRemovableExtDom.cauchy_interior_dom, and the     *)
(*  continuity hypothesis is pointwise (Fptc), from which CcontC f =     *)
(*  ptcont_CcontC f Fptc.  Axiom-clean.                               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral
        CGoursatLin CLeibniz CWinding CDeriv Holomorphic RootsOfUnity CTaylor
        CWindingOffCenter CTaylorRem PerronRemovable CRemovableExtDom.
Open Scope R_scope.

Section TaylorRemDom.
Variable Rr : R.
Variable f : C -> C.
Variable w : C.
Hypothesis HR : 0 < Rr.
Hypothesis Hfhol_disk : forall z, Cmod z < Rr + 1 -> exists d, is_Cderiv f z d.
Hypothesis Fptc : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (f z') (f z)) < eps.
Hypothesis Hw : Cmod w < Rr.
Hypothesis Hfbd : exists Mf, 0 <= Mf /\ forall u, Cmod (f (arc Rr u)) <= Mf.

Definition Hfcc : CcontC f := ptcont_CcontC f Fptc.

(* the circle never hits 0 or w *)
Lemma arc_ne0_D : forall u, arc Rr u <> C0.
Proof.
  intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra.
Qed.

Lemma arcw_ne_D : forall u, Cminus (arc Rr u) w <> C0.
Proof.
  intros u Hc.
  assert (Hle : Rr - Cmod w <= Cmod (Cminus (arc Rr u) w)).
  { eapply Rle_trans; [ | apply Cmod_rev_triangle ]. rewrite (Cmod_arc Rr u) by lra. lra. }
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hle. lra.
Qed.

Lemma arcpow_ne0_D : forall k u, Cpow (arc Rr u) k <> C0.
Proof. intros k u; apply Cpow_ne0, arc_ne0_D. Qed.

(* ---- the three integrand families ---- *)
Definition pki_D (k : nat) (u : R) : C :=          (* a_k integrand:  f/z^{k+1} . z' *)
  Cmul (Cmul (f (arc Rr u)) (Cinv (Cpow (arc Rr u) (S k)))) (arc' Rr u).
Definition cci_D (k : nat) (u : R) : C :=          (* w^k . f/z^{k+1} . z' *)
  Cmul (Cmul (f (arc Rr u)) (tterm w (arc Rr u) k)) (arc' Rr u).
Definition rri_D (n : nat) (u : R) : C :=          (* remainder:  f . trem . z' *)
  Cmul (Cmul (f (arc Rr u)) (trem w (arc Rr u) n)) (arc' Rr u).
Definition kki_D (u : R) : C :=                    (* full kernel:  f/(z-w) . z' *)
  Cmul (Cmul (f (arc Rr u)) (Cinv (Cminus (arc Rr u) w))) (arc' Rr u).

Lemma Cpow_arc_cont_D : forall k, Ccont (fun u => Cpow (arc Rr u) k).
Proof.
  induction k as [|k IH]; cbn [Cpow].
  - apply Ccont_const.
  - apply Ccont_mul; [ exact (Ccont_arc Rr) | exact IH ].
Qed.

Lemma Hpki_D : forall k, Ccont (pki_D k).
Proof.
  intro k; unfold pki_D. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont_D (S k)) | intro u; apply arcpow_ne0_D ].
Qed.

Lemma Hcci_D : forall k, Ccont (cci_D k).
Proof.
  intro k; unfold cci_D, tterm. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont_D (S k)) | intro u; apply arcpow_ne0_D ].
Qed.

Lemma Hrri_D : forall n, Ccont (rri_D n).
Proof.
  intro n; unfold rri_D, trem. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  apply Ccont_inv;
    [ apply Ccont_mul;
        [ exact (Cpow_arc_cont_D n)
        | apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ] ]
    | intro u; apply Cmul_ne0; [ apply arcpow_ne0_D | apply arcw_ne_D ] ].
Qed.

Lemma Hkki_D : Ccont kki_D.
Proof.
  unfold kki_D. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv;
    [ apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ] | apply arcw_ne_D ].
Qed.

(* ---- cci_D relates to pki_D by the constant w^k ---- *)
Lemma cci_pki_D : forall k u, cci_D k u = Cmul (Cpow w k) (pki_D k u).
Proof. intros k u; unfold cci_D, pki_D, tterm; ring. Qed.

(* ---- the pointwise geometric split of the full-kernel integrand ---- *)
Lemma kki_split_D : forall n u,
  kki_D u = Cadd (Csum (fun k => cci_D k u) n) (rri_D n u).
Proof.
  intros n u. unfold kki_D, cci_D, rri_D.
  rewrite (kernel_geom w (arc Rr u) n (arc_ne0_D u) (arcw_ne_D u)).
  rewrite <- (distrib (f (arc Rr u)) (arc' Rr u) (tterm w (arc Rr u)) n).
  ring.
Qed.

(* ---- B1: the full-kernel integral is 2 pi i . f(w) ---- *)
Lemma kki_cauchy_D : Cintf kki_D Hkki_D 0 (2 * PI) = Cmul (mkC 0 (2 * PI)) (f w).
Proof.
  destruct (Hfhol_disk w ltac:(lra)) as [dw Hdw].
  exact (cauchy_interior_dom f Rr w dw HR Hw Hdw Fptc
           (fun z Hzd (_ : z <> w) => Hfhol_disk z Hzd) Hkki_D).
Qed.

(* ---- the split, integrated ---- *)
Lemma taylor_remainder_D : forall n,
  Cmul (mkC 0 (2 * PI)) (f w)
  = Cadd (Csum (fun k => Cintf (cci_D k) (Hcci_D k) 0 (2 * PI)) n)
         (Cintf (rri_D n) (Hrri_D n) 0 (2 * PI)).
Proof.
  intro n.
  rewrite <- kki_cauchy_D.
  assert (Hsum : Ccont (fun u => Csum (fun k => cci_D k u) n))
    by (apply Ccont_Csum; intro k; apply Hcci_D).
  rewrite (Cintf_ext kki_D (fun u => Cadd (Csum (fun k => cci_D k u) n) (rri_D n u))
             Hkki_D (Ccont_add _ _ Hsum (Hrri_D n)) 0 (2 * PI) (fun u => kki_split_D n u)).
  rewrite (Cintf_add (fun u => Csum (fun k => cci_D k u) n) (rri_D n)
             Hsum (Hrri_D n) (Ccont_add _ _ Hsum (Hrri_D n)) 0 (2 * PI)
             ltac:(generalize PI_RGT_0; lra)).
  rewrite (Cintf_Csum cci_D n Hcci_D Hsum 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
  reflexivity.
Qed.

(* ---- ML bound on the remainder ---- *)
Lemma rem_ML_D : forall n Mf, 0 <= Mf -> (forall u, Cmod (f (arc Rr u)) <= Mf) ->
  Cmod (Cintf (rri_D n) (Hrri_D n) 0 (2 * PI))
  <= 2 * (Mf * Rr / (Rr - Cmod w) * (Cmod w / Rr) ^ n) * (2 * PI - 0).
Proof.
  intros n Mf HMf Hbd.
  set (d := Rr - Cmod w).
  assert (Hd : 0 < d) by (unfold d; lra).
  assert (Hmw : 0 <= Cmod w) by apply Cmod_nonneg.
  change (Cintf (rri_D n) (Hrri_D n) 0 (2 * PI))
    with (pathint (arc Rr) (arc' Rr) (fun z => Cmul (f z) (trem w z n)) (Hrri_D n) 0 (2 * PI)).
  apply (pathint_ML (arc Rr) (arc' Rr) (fun z => Cmul (f z) (trem w z n)) (Hrri_D n)
           0 (2 * PI) (Mf * Rr / d * (Cmod w / Rr) ^ n)
           ltac:(generalize PI_RGT_0; lra)).
  intros u _.
  (* pointwise: Cmod (f . trem . z') <= Mf Rr/d rho^n *)
  change (Cmul (Cmul (f (arc Rr u)) (trem w (arc Rr u) n)) (arc' Rr u))
    with (rri_D n u); unfold rri_D.
  rewrite Cmod_mul, (Cmod_arc' Rr u ltac:(lra)), Cmod_mul.
  unfold trem. rewrite Cmod_mul, Cmod_Cpow.
  assert (HXne : Cmul (Cpow (arc Rr u) n) (Cminus (arc Rr u) w) <> C0)
    by (apply Cmul_ne0; [ apply arcpow_ne0_D | apply arcw_ne_D ]).
  rewrite (Cmod_inv _ HXne), Cmod_mul, Cmod_Cpow, (Cmod_arc Rr u ltac:(lra)).
  (* now: Cmod(f) * (Cmod w^n * / (Rr^n * Cmod(arc-w))) * Rr <= Mf Rr/d rho^n *)
  set (A := Cmod (f (arc Rr u))). set (B := Cmod (Cminus (arc Rr u) w)).
  assert (HA0 : 0 <= A) by apply Cmod_nonneg.
  assert (HAM : A <= Mf) by apply Hbd.
  assert (HB : d <= B).
  { unfold B, d. eapply Rle_trans; [ | apply Cmod_rev_triangle ].
    rewrite (Cmod_arc Rr u) by lra. lra. }
  assert (HBpos : 0 < B) by lra.
  assert (Hrrn : 0 < Rr ^ n) by (apply pow_lt; lra).
  assert (Hwn : 0 <= Cmod w ^ n) by (apply pow_le; exact Hmw).
  rewrite (pow_div (Cmod w) Rr n ltac:(lra)).
  (* goal: A * (Cmod w^n * / (Rr^n * B)) * Rr <= Mf * Rr / d * (Cmod w^n / Rr^n) *)
  apply Rle_trans with (Mf * (Cmod w ^ n * / (Rr ^ n * d)) * Rr).
  - apply Rmult_le_compat_r; [ lra | ].
    apply Rmult_le_compat; [ exact HA0 | | exact HAM | ].
    + apply Rmult_le_pos; [ exact Hwn | left; apply Rinv_0_lt_compat, Rmult_lt_0_compat; lra ].
    + apply Rmult_le_compat_l; [ exact Hwn | ].
      apply Rinv_le_contravar; [ apply Rmult_lt_0_compat; lra | ].
      apply Rmult_le_compat_l; [ left; exact Hrrn | exact HB ].
  - apply Req_le. field. split; lra.
Qed.

(* ================================================================= *)
(*  B4 (centre form): all Taylor coefficients zero => f(w) = 0         *)
(* ================================================================= *)
Theorem taylor_center_zero_D :
  (forall k, Cintf (pki_D k) (Hpki_D k) 0 (2 * PI) = C0) ->
  f w = C0.
Proof.
  intro Hak.
  destruct Hfbd as [Mf [HMf Hbd]].
  (* each cci_D-integral vanishes: oint cci_k = w^k . a_k = 0 *)
  assert (Hcci0 : forall k, Cintf (cci_D k) (Hcci_D k) 0 (2 * PI) = C0).
  { intro k.
    rewrite (Cintf_ext (cci_D k) (fun u => Cmul (Cpow w k) (pki_D k u)) (Hcci_D k)
               (Ccont_scal (Cpow w k) (pki_D k) (Hpki_D k)) 0 (2 * PI) (cci_pki_D k)).
    rewrite (Cintf_cmul_l (Cpow w k) (pki_D k) (Hpki_D k)
               (Ccont_scal (Cpow w k) (pki_D k) (Hpki_D k)) 0 (2 * PI)
               ltac:(generalize PI_RGT_0; lra)).
    rewrite (Hak k). ring. }
  (* so 2 pi i f(w) = remainder, for every n *)
  assert (Hfw : forall n, Cmul (mkC 0 (2 * PI)) (f w) = Cintf (rri_D n) (Hrri_D n) 0 (2 * PI)).
  { intro n. rewrite (taylor_remainder_D n).
    rewrite (Csum_ext (fun k => Cintf (cci_D k) (Hcci_D k) 0 (2 * PI)) (fun _ => C0) n Hcci0).
    rewrite Csum_zero. ring. }
  (* modulus: 2 pi |f(w)| <= K rho^n -> 0 *)
  set (rho := Cmod w / Rr).
  assert (Hrho0 : 0 <= rho) by (unfold rho; apply Rle_mult_inv_pos; [ apply Cmod_nonneg | lra ]).
  assert (Hrho1 : rho < 1) by (unfold rho, Rdiv; apply Rmult_lt_reg_r with Rr; [ lra | ];
    rewrite Rmult_assoc, Rinv_l by lra; lra).
  assert (Hbound : forall n, 2 * PI * Cmod (f w)
                    <= (2 * (Mf * Rr / (Rr - Cmod w)) * (2 * PI)) * rho ^ n).
  { intro n.
    assert (He : 2 * PI * Cmod (f w) = Cmod (Cmul (mkC 0 (2 * PI)) (f w))).
    { rewrite Cmod_mul. f_equal.
      unfold Cmod, Cnorm2; cbn [Re Im]. rewrite Rmult_0_l, Rplus_0_l.
      rewrite sqrt_square; [ reflexivity | generalize PI_RGT_0; lra ]. }
    rewrite He, (Hfw n).
    eapply Rle_trans; [ apply (rem_ML_D n Mf HMf Hbd) | ].
    unfold rho. apply Req_le. ring. }
  assert (Hzero : 2 * PI * Cmod (f w) = 0).
  { apply (le_all_pow_zero (2 * PI * Cmod (f w))
             (2 * (Mf * Rr / (Rr - Cmod w)) * (2 * PI)) rho).
    - generalize PI_RGT_0; pose proof (Cmod_nonneg (f w)); nra.
    - exact Hrho0.
    - exact Hrho1.
    - assert (0 <= Mf * Rr / (Rr - Cmod w))
        by (apply Rle_mult_inv_pos; [ apply Rmult_le_pos; lra | lra ]).
      generalize PI_RGT_0; nra.
    - exact Hbound. }
  assert (Hcm : Cmod (f w) = 0) by (generalize PI_RGT_0; nra).
  apply (proj1 (Cmod0 (f w))); exact Hcm.
Qed.

End TaylorRemDom.

Print Assumptions taylor_center_zero_D.
