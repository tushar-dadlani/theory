(* ================================================================= *)
(*  CTaylorRem.v  (identity-theorem plan, brick B3 assembly + B4)      *)
(*                                                                    *)
(*  Taylor-with-remainder at centre 0 and the vanishing theorem B4:    *)
(*  for f holomorphic on a disk containing |z|<=R and |w|<R,           *)
(*    2 pi i . f(w) = sum_{k<n} w^k . a_k  +  w^n . oint f/(z^n(z-w)),  *)
(*  with a_k = oint_{|z|=R} f(z)/z^{k+1} dz.  The remainder is         *)
(*  ML-bounded by K.rho^n with rho = |w|/R < 1, so it -> 0; hence      *)
(*                                                                    *)
(*     (forall k, a_k = 0)  =>  f(w) = 0.        (B4, centre form)      *)
(*                                                                    *)
(*  Built from B1 (CCauchyFull.cauchy_interior), B3-core (CTaylor:      *)
(*  kernel_geom, Cintf_Csum), and pathint_ML.  Axiom-clean.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral
        CGoursatLin CLeibniz CWinding CDeriv Holomorphic RootsOfUnity CTaylor
        CWindingOffCenter CCauchyFull.
Open Scope R_scope.

(* ---- Cmod of a power (proved locally to avoid a heavy import) ---- *)
Lemma Cmod_Cpow : forall a k, Cmod (Cpow a k) = (Cmod a) ^ k.
Proof.
  intros a k; induction k as [|k IH]; cbn [Cpow pow].
  - apply Cmod_C1.
  - rewrite Cmod_mul, IH; reflexivity.
Qed.

(* ---- real helpers ---- *)
Lemma pow_div : forall a b n, b <> 0 -> (a / b) ^ n = a ^ n / b ^ n.
Proof.
  intros a b n Hb; induction n as [|n IH]; cbn [pow].
  - field.
  - rewrite IH; field; split; [ apply pow_nonzero; exact Hb | exact Hb ].
Qed.

Lemma le_all_pow_zero : forall X K r, 0 <= X -> 0 <= r -> r < 1 -> 0 <= K ->
  (forall n, X <= K * r ^ n) -> X = 0.
Proof.
  intros X K r HX Hr0 Hr1 HK Hle.
  assert (HX0 : X <= 0).
  { destruct (Rle_lt_dec X 0) as [Hle0 | Hpos]; [ exact Hle0 | exfalso ].
    destruct (Req_dec K 0) as [HK0 | HKn].
    - specialize (Hle 1%nat). rewrite HK0 in Hle. lra.
    - assert (HKpos : 0 < K) by lra.
      destruct (pow_lt_1_zero r ltac:(rewrite Rabs_right; lra) (X / K)
                  ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
      specialize (HN N (le_n N)). specialize (Hle N).
      rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra).
      assert (K * r ^ N < X) by (replace X with (K * (X / K)) by (field; lra);
        apply Rmult_lt_compat_l; [ exact HKpos | exact HN ]). lra. }
  lra.
Qed.

(* ---- Csum helpers ---- *)
Lemma Csum_zero : forall n, Csum (fun _ => C0) n = C0.
Proof. induction n as [|n IH]; cbn [Csum]; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma distrib : forall a b g n,
  Cmul (Cmul a (Csum g n)) b = Csum (fun k => Cmul (Cmul a (g k)) b) n.
Proof.
  intros a b g n; induction n as [|n IH]; cbn [Csum].
  - ring.
  - rewrite <- IH; ring.
Qed.

Section TaylorRem.
Variable Rr : R.
Variable f : C -> C.
Variable w : C.
Hypothesis HR : 0 < Rr.
Hypothesis Hfhol : forall z, exists d, is_Cderiv f z d.
Hypothesis Hfcc : CcontC f.
Hypothesis Hw : Cmod w < Rr.
Hypothesis Hfbd : exists Mf, 0 <= Mf /\ forall u, Cmod (f (arc Rr u)) <= Mf.

(* the circle never hits 0 or w *)
Lemma arc_ne0 : forall u, arc Rr u <> C0.
Proof.
  intros u Hc. assert (HM : Cmod (arc Rr u) = Rr) by (apply Cmod_arc; lra).
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in HM. lra.
Qed.

Lemma arcw_ne : forall u, Cminus (arc Rr u) w <> C0.
Proof.
  intros u Hc.
  assert (Hle : Rr - Cmod w <= Cmod (Cminus (arc Rr u) w)).
  { eapply Rle_trans; [ | apply Cmod_rev_triangle ]. rewrite (Cmod_arc Rr u) by lra. lra. }
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hle. lra.
Qed.

Lemma arcpow_ne0 : forall k u, Cpow (arc Rr u) k <> C0.
Proof. intros k u; apply Cpow_ne0, arc_ne0. Qed.

(* ---- the three integrand families ---- *)
Definition pki (k : nat) (u : R) : C :=          (* a_k integrand:  f/z^{k+1} . z' *)
  Cmul (Cmul (f (arc Rr u)) (Cinv (Cpow (arc Rr u) (S k)))) (arc' Rr u).
Definition cci (k : nat) (u : R) : C :=          (* w^k . f/z^{k+1} . z' *)
  Cmul (Cmul (f (arc Rr u)) (tterm w (arc Rr u) k)) (arc' Rr u).
Definition rri (n : nat) (u : R) : C :=          (* remainder:  f . trem . z' *)
  Cmul (Cmul (f (arc Rr u)) (trem w (arc Rr u) n)) (arc' Rr u).
Definition kki (u : R) : C :=                    (* full kernel:  f/(z-w) . z' *)
  Cmul (Cmul (f (arc Rr u)) (Cinv (Cminus (arc Rr u) w))) (arc' Rr u).

Lemma Cpow_arc_cont : forall k, Ccont (fun u => Cpow (arc Rr u) k).
Proof.
  induction k as [|k IH]; cbn [Cpow].
  - apply Ccont_const.
  - apply Ccont_mul; [ exact (Ccont_arc Rr) | exact IH ].
Qed.

Lemma Hpki : forall k, Ccont (pki k).
Proof.
  intro k; unfold pki. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont (S k)) | intro u; apply arcpow_ne0 ].
Qed.

Lemma Hcci : forall k, Ccont (cci k).
Proof.
  intro k; unfold cci, tterm. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  apply Ccont_inv; [ exact (Cpow_arc_cont (S k)) | intro u; apply arcpow_ne0 ].
Qed.

Lemma Hrri : forall n, Ccont (rri n).
Proof.
  intro n; unfold rri, trem. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_mul; [ apply Ccont_const | ].
  apply Ccont_inv;
    [ apply Ccont_mul;
        [ exact (Cpow_arc_cont n)
        | apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ] ]
    | intro u; apply Cmul_ne0; [ apply arcpow_ne0 | apply arcw_ne ] ].
Qed.

Lemma Hkki : Ccont kki.
Proof.
  unfold kki. apply Ccont_mul; [ | apply Ccont_arc' ].
  apply Ccont_mul; [ exact (Hfcc (arc Rr) (Ccont_arc Rr)) | ].
  apply Ccont_inv;
    [ apply Ccont_minus; [ exact (Ccont_arc Rr) | apply Ccont_const ] | apply arcw_ne ].
Qed.

(* ---- cci relates to pki by the constant w^k ---- *)
Lemma cci_pki : forall k u, cci k u = Cmul (Cpow w k) (pki k u).
Proof. intros k u; unfold cci, pki, tterm; ring. Qed.

(* ---- the pointwise geometric split of the full-kernel integrand ---- *)
Lemma kki_split : forall n u,
  kki u = Cadd (Csum (fun k => cci k u) n) (rri n u).
Proof.
  intros n u. unfold kki, cci, rri.
  rewrite (kernel_geom w (arc Rr u) n (arc_ne0 u) (arcw_ne u)).
  rewrite <- (distrib (f (arc Rr u)) (arc' Rr u) (tterm w (arc Rr u)) n).
  ring.
Qed.

(* ---- B1: the full-kernel integral is 2 pi i . f(w) ---- *)
Lemma kki_cauchy : Cintf kki Hkki 0 (2 * PI) = Cmul (mkC 0 (2 * PI)) (f w).
Proof.
  destruct (Hfhol w) as [dw Hdw].
  exact (cauchy_interior f Rr w dw Hfhol Hdw HR Hw Hkki).
Qed.

(* ---- the split, integrated ---- *)
Lemma taylor_remainder : forall n,
  Cmul (mkC 0 (2 * PI)) (f w)
  = Cadd (Csum (fun k => Cintf (cci k) (Hcci k) 0 (2 * PI)) n)
         (Cintf (rri n) (Hrri n) 0 (2 * PI)).
Proof.
  intro n.
  rewrite <- kki_cauchy.
  assert (Hsum : Ccont (fun u => Csum (fun k => cci k u) n))
    by (apply Ccont_Csum; intro k; apply Hcci).
  rewrite (Cintf_ext kki (fun u => Cadd (Csum (fun k => cci k u) n) (rri n u))
             Hkki (Ccont_add _ _ Hsum (Hrri n)) 0 (2 * PI) (fun u => kki_split n u)).
  rewrite (Cintf_add (fun u => Csum (fun k => cci k u) n) (rri n)
             Hsum (Hrri n) (Ccont_add _ _ Hsum (Hrri n)) 0 (2 * PI)
             ltac:(generalize PI_RGT_0; lra)).
  rewrite (Cintf_Csum cci n Hcci Hsum 0 (2 * PI) ltac:(generalize PI_RGT_0; lra)).
  reflexivity.
Qed.

(* ---- ML bound on the remainder ---- *)
Lemma rem_ML : forall n Mf, 0 <= Mf -> (forall u, Cmod (f (arc Rr u)) <= Mf) ->
  Cmod (Cintf (rri n) (Hrri n) 0 (2 * PI))
  <= 2 * (Mf * Rr / (Rr - Cmod w) * (Cmod w / Rr) ^ n) * (2 * PI - 0).
Proof.
  intros n Mf HMf Hbd.
  set (d := Rr - Cmod w).
  assert (Hd : 0 < d) by (unfold d; lra).
  assert (Hmw : 0 <= Cmod w) by apply Cmod_nonneg.
  change (Cintf (rri n) (Hrri n) 0 (2 * PI))
    with (pathint (arc Rr) (arc' Rr) (fun z => Cmul (f z) (trem w z n)) (Hrri n) 0 (2 * PI)).
  apply (pathint_ML (arc Rr) (arc' Rr) (fun z => Cmul (f z) (trem w z n)) (Hrri n)
           0 (2 * PI) (Mf * Rr / d * (Cmod w / Rr) ^ n)
           ltac:(generalize PI_RGT_0; lra)).
  intros u _.
  (* pointwise: Cmod (f . trem . z') <= Mf Rr/d rho^n *)
  change (Cmul (Cmul (f (arc Rr u)) (trem w (arc Rr u) n)) (arc' Rr u))
    with (rri n u); unfold rri.
  rewrite Cmod_mul, (Cmod_arc' Rr u ltac:(lra)), Cmod_mul.
  unfold trem. rewrite Cmod_mul, Cmod_Cpow.
  assert (HXne : Cmul (Cpow (arc Rr u) n) (Cminus (arc Rr u) w) <> C0)
    by (apply Cmul_ne0; [ apply arcpow_ne0 | apply arcw_ne ]).
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
Theorem taylor_center_zero :
  (forall k, Cintf (pki k) (Hpki k) 0 (2 * PI) = C0) ->
  f w = C0.
Proof.
  intro Hak.
  destruct Hfbd as [Mf [HMf Hbd]].
  (* each cci-integral vanishes: oint cci_k = w^k . a_k = 0 *)
  assert (Hcci0 : forall k, Cintf (cci k) (Hcci k) 0 (2 * PI) = C0).
  { intro k.
    rewrite (Cintf_ext (cci k) (fun u => Cmul (Cpow w k) (pki k u)) (Hcci k)
               (Ccont_scal (Cpow w k) (pki k) (Hpki k)) 0 (2 * PI) (cci_pki k)).
    rewrite (Cintf_cmul_l (Cpow w k) (pki k) (Hpki k)
               (Ccont_scal (Cpow w k) (pki k) (Hpki k)) 0 (2 * PI)
               ltac:(generalize PI_RGT_0; lra)).
    rewrite (Hak k). ring. }
  (* so 2 pi i f(w) = remainder, for every n *)
  assert (Hfw : forall n, Cmul (mkC 0 (2 * PI)) (f w) = Cintf (rri n) (Hrri n) 0 (2 * PI)).
  { intro n. rewrite (taylor_remainder n).
    rewrite (Csum_ext (fun k => Cintf (cci k) (Hcci k) 0 (2 * PI)) (fun _ => C0) n Hcci0).
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
    eapply Rle_trans; [ apply (rem_ML n Mf HMf Hbd) | ].
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

End TaylorRem.

Print Assumptions taylor_center_zero.
