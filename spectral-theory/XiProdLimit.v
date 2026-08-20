(* ================================================================= *)
(*  XiProdLimit.v  —  piece 1: the cofactor sequence CONVERGES.        *)
(*                                                                    *)
(*    hadamard_prod_ne0 : the limit product is NONZERO away from the   *)
(*      zeros -- the one genuinely new estimate left;                  *)
(*    Hseq_cv          : hence  Hseq N z := xi z / Pprod N z           *)
(*      converges to  xi z / P z.                                      *)
(*                                                                    *)
(*  XiProdFactor gave xi = H_N . Pprod_N exactly, at every N, with the  *)
(*  divergent constant and the divergent exponential both absorbed into *)
(*  H_N.  Since Pprod_N converges and xi is fixed, H_N is FORCED to     *)
(*  converge -- provided the limit product is nonzero, which is what    *)
(*  this file supplies.                                                *)
(*                                                                    *)
(*  WHY THE LIMIT PRODUCT IS NONZERO.  Split at M: the head Pprod f M   *)
(*  is a finite product of nonzero factors, and the TAIL products stay  *)
(*  within exp(tail) - 1 of 1.  Choosing M so that the deviation tail   *)
(*  is under 1/(2e) makes exp(tail) - 1 < 1/2, so every tail product    *)
(*  has modulus >= 1/2 and the whole partial product is bounded below   *)
(*  by |Pprod f M|/2 > 0 -- a bound independent of how far out one      *)
(*  goes.  A limit of things bounded below by c is >= c.               *)
(*                                                                    *)
(*  H_N is NOT extracted from XiProdFactor's existential -- that would  *)
(*  need choice.  Hseq is defined outright as xi z . (Pprod N z)^{-1},  *)
(*  and Hseq_eq identifies it with the entire H wherever Pprod N is     *)
(*  nonzero.  Axiom-clean.                                             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CDeriv CexpFull CSeries CInfProd
        CRemovableExtDom XiZeroEnum XiHadamardProd XiHadamardUnif XiProdFactor
        RiemannXiEntire.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  factors are nonzero off the zero set                          *)
(* ----------------------------------------------------------------- *)
Lemma Efac_ne0 : forall z rho, rho <> C0 -> z <> rho -> Efac z rho <> C0.
Proof.
  intros z rho Hr Hz. unfold Efac.
  apply Cmul_ne0; [ | apply Cexpf_ne0 ].
  intro Hc. apply Hz.
  assert (Hzr : Cmul z (Cinv rho) = C1).
  { replace (Cmul z (Cinv rho))
      with (Cminus C1 (Cminus C1 (Cmul z (Cinv rho)))) by ring.
    rewrite Hc. ring. }
  transitivity (Cmul (Cmul z (Cinv rho)) rho).
  - field. exact Hr.
  - rewrite Hzr. ring.
Qed.

Lemma Pprod_ne0 : forall (f : nat -> C) (N : nat),
  (forall k, f k <> C0) -> Pprod f N <> C0.
Proof.
  intros f N Hf. induction N as [| N IH]; cbn [Pprod];
    [ apply Hf | apply Cmul_ne0; [ exact IH | apply Hf ] ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  a limit of things bounded below is bounded below              *)
(* ----------------------------------------------------------------- *)
Lemma CUn_cv_mod_ge : forall (u : nat -> C) (l : C) (c : R) (N0 : nat),
  CUn_cv u l -> (forall n, (N0 <= n)%nat -> c <= Cmod (u n)) -> c <= Cmod l.
Proof.
  intros u l c N0 Hcv Hge.
  destruct (Rle_or_lt c (Cmod l)) as [Hle | Hlt]; [ exact Hle | exfalso ].
  destruct (Hcv (c - Cmod l) ltac:(lra)) as [N1 HN1].
  set (n := Nat.max N0 N1).
  pose proof (HN1 n ltac:(unfold n; lia)) as Hclose.
  pose proof (Hge n ltac:(unfold n; lia)) as Hbig.
  assert (Htri : Cmod (u n) <= Cmod l + Cmod (Cminus (u n) l)).
  { replace (u n) with (Cadd l (Cminus (u n) l)) at 1 by ring.
    apply Cmod_triangle. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  THE LIMIT PRODUCT IS NONZERO                                   *)
(* ----------------------------------------------------------------- *)
Theorem hadamard_prod_ne0 : forall (rho : nat -> C),
  ZeroEnum rho -> (forall n, 1 <= Cmod (rho n)) ->
  forall z, (forall n, z <> rho n) ->
  forall P, CUn_cv (Pprod (fun k => Efac z (rho k))) P -> P <> C0.
Proof.
  intros rho Henum Hlow z Hz P HP.
  set (f := fun k => Efac z (rho k)).
  assert (Hfne : forall k, f k <> C0).
  { intro k. unfold f. apply Efac_ne0; [ | apply Hz ].
    intro Hc. pose proof (Hlow k) as Hl.
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hl. lra. }
  destruct (Efac_devsum_cv rho Henum Hlow z) as [T HT].
  fold f in HT.
  pose proof (exp_pos 1) as Hp1.
  (* choose M so the deviation tail is under 1/(2e) *)
  set (u0 := Rmin 1 (/ (2 * exp 1))).
  assert (Hu0 : 0 < u0)
    by (apply Rmin_glb_lt; [ lra | apply Rinv_0_lt_compat; lra ]).
  destruct (HT u0 Hu0) as [M HM]. specialize (HM M (le_n M)).
  set (tl := T - sum_f_R0 (dev f) M).
  pose proof (sum_dev_le_T f T HT M) as HsM.
  assert (Htl0 : 0 <= tl) by (unfold tl; lra).
  assert (Htlu : tl < u0).
  { unfold tl. unfold R_dist in HM. rewrite Rabs_left1 in HM by lra. lra. }
  (* hence exp tl - 1 < 1/2 *)
  assert (Hexptl : exp tl - 1 < / 2).
  { assert (H1 : tl <= 1)
      by (pose proof (Rmin_l 1 (/ (2 * exp 1))); unfold u0 in Htlu; lra).
    assert (H2 : tl < / (2 * exp 1))
      by (pose proof (Rmin_r 1 (/ (2 * exp 1))); unfold u0 in Htlu; lra).
    pose proof (exp_m1_le tl Htl0) as He.
    assert (Hexp1 : exp tl <= exp 1) by (apply exp_le; exact H1).
    assert (Hkey : / (2 * exp 1) * exp 1 = / 2) by (field; lra).
    nra. }
  (* every tail product has modulus at least 1/2 *)
  assert (Htail : forall k, / 2 <= Cmod (Pprod (fun j => f (S (M + j))) k)).
  { intro k.
    assert (Hb : Cmod (Cminus (Pprod (fun j => f (S (M + j))) k) C1) <= exp tl - 1).
    { eapply Rle_trans; [ apply Pprod_dev_bound | ].
      apply Rplus_le_compat_r.
      eapply Rle_trans;
        [ apply (RPdev_le_exp (dev (fun j => f (S (M + j)))) (dev_nonneg _)) | ].
      apply exp_le.
      change (dev (fun j => f (S (M + j)))) with (fun j => dev f (S (M + j))).
      assert (Heq : sum_f_R0 (fun j => dev f (S (M + j))) k
                  = sum_f_R0 (dev f) (S (M + k)) - sum_f_R0 (dev f) M)
        by (apply (sumtail_eq (dev f) M k)).
      rewrite Heq. unfold tl.
      pose proof (sum_dev_le_T f T HT (S (M + k))). lra. }
    pose proof (Cmod_diff_le (Pprod (fun j => f (S (M + j))) k) C1) as Hd.
    rewrite Cmod_C1 in Hd.
    assert (Habs : Rabs (Cmod (Pprod (fun j => f (S (M + j))) k) - 1) < / 2) by lra.
    destruct (Rabs_def2 _ _ Habs). lra. }
  (* the head product is nonzero, so the whole thing is bounded below *)
  assert (HM0 : Pprod f M <> C0) by (apply Pprod_ne0; exact Hfne).
  assert (HMpos : 0 < Cmod (Pprod f M)).
  { destruct (Cmod_nonneg (Pprod f M)) as [Hgt | Heq]; [ exact Hgt | exfalso ].
    apply HM0. apply (proj1 (Cmod0 _)). symmetry. exact Heq. }
  set (c := Cmod (Pprod f M) * / 2).
  assert (Hc : 0 < c) by (unfold c; lra).
  assert (Hge : forall n, (S M <= n)%nat -> c <= Cmod (Pprod f n)).
  { intros n Hn.
    assert (Hk : exists k, n = S (M + k)%nat) by (exists (n - M - 1)%nat; lia).
    destruct Hk as [k ->].
    rewrite Pprod_split, Cmod_mul. unfold c.
    apply Rmult_le_compat_l; [ apply Cmod_nonneg | apply Htail ]. }
  pose proof (CUn_cv_mod_ge (Pprod f) P c (S M) HP Hge) as Hfin.
  intro HP0. rewrite HP0, (proj2 (Cmod0 C0) eq_refl) in Hfin. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  limit arithmetic: inverse and constant multiple                *)
(* ----------------------------------------------------------------- *)
Lemma CUn_cv_scal : forall (c : C) (u : nat -> C) (l : C),
  CUn_cv u l -> CUn_cv (fun n => Cmul c (u n)) (Cmul c l).
Proof.
  intros c u l Hcv eps Heps.
  pose proof (Cmod_nonneg c) as Hc0.
  destruct (Hcv (eps / (Cmod c + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  exists N. intros n Hn. pose proof (HN n Hn) as H.
  replace (Cminus (Cmul c (u n)) (Cmul c l)) with (Cmul c (Cminus (u n) l)) by ring.
  rewrite Cmod_mul.
  assert (Hlt : Cmod c * (eps / (Cmod c + 1)) < eps).
  { apply (Rmult_lt_reg_r (Cmod c + 1)); [ lra | ].
    replace (Cmod c * (eps / (Cmod c + 1)) * (Cmod c + 1)) with (Cmod c * eps)
      by (field; lra). nra. }
  assert (Hle : Cmod c * Cmod (Cminus (u n) l) <= Cmod c * (eps / (Cmod c + 1)))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Lemma CUn_cv_inv : forall (u : nat -> C) (l : C),
  CUn_cv u l -> l <> C0 -> (forall n, u n <> C0) ->
  CUn_cv (fun n => Cinv (u n)) (Cinv l).
Proof.
  intros u l Hcv Hl Hu eps Heps.
  assert (Hml : 0 < Cmod l).
  { destruct (Cmod_nonneg l) as [Hgt | Heq]; [ exact Hgt | exfalso ].
    apply Hl. apply (proj1 (Cmod0 _)). symmetry. exact Heq. }
  destruct (Hcv (Cmod l / 2) ltac:(lra)) as [N1 HN1].
  assert (Hll : 0 < Cmod l * Cmod l) by (apply Rmult_lt_0_compat; exact Hml).
  destruct (Hcv (eps * (Cmod l * Cmod l) / 2)
             ltac:(apply Rdiv_lt_0_compat;
                   [ apply Rmult_lt_0_compat; [ exact Heps | exact Hll ] | lra ]))
    as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  pose proof (HN1 n ltac:(lia)) as H1.
  pose proof (HN2 n ltac:(lia)) as H2.
  (* Cmod (u n) stays above Cmod l / 2 *)
  pose proof (Cmod_diff_le (u n) l) as Hd.
  destruct (Rabs_def2 _ _ (Rle_lt_trans _ _ _ Hd H1)) as [Hlo Hhi].
  assert (Hun : Cmod l / 2 < Cmod (u n)) by lra.
  assert (Hunpos : 0 < Cmod (u n)) by lra.
  assert (Hune : Cmul (u n) l <> C0) by (apply Cmul_ne0; [ apply Hu | exact Hl ]).
  rewrite (Cinv_diff (u n) l (Hu n) Hl), Cmod_mul, (Cmod_inv _ Hune), Cmod_mul.
  rewrite (Cmod_minus_sym l (u n)).
  (* |u n - l| / (|u n| |l|) < eps *)
  assert (Hprod : 0 < Cmod (u n) * Cmod l)
    by (apply Rmult_lt_0_compat; [ exact Hunpos | exact Hml ]).
  assert (Hprodne : Cmod (u n) * Cmod l <> 0) by lra.
  apply (Rmult_lt_reg_r (Cmod (u n) * Cmod l)); [ exact Hprod | ].
  replace (Cmod (Cminus (u n) l) * / (Cmod (u n) * Cmod l) * (Cmod (u n) * Cmod l))
    with (Cmod (Cminus (u n) l)) by (field; split; apply Rgt_not_eq; lra).
  assert (Hq : (Cmod l * Cmod l) / 2 <= Cmod (u n) * Cmod l) by nra.
  assert (Hstep : eps * ((Cmod l * Cmod l) / 2) <= eps * (Cmod (u n) * Cmod l))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(* ================================================================= *)
(*  E.  THE COFACTOR SEQUENCE AND ITS LIMIT                            *)
(* ================================================================= *)
Definition Hseq (rho : nat -> C) (N : nat) (z : C) : C :=
  Cmul (XiC z) (Cinv (Pprod (fun k => Efac z (rho k)) N)).

(* Hseq IS the entire cofactor of XiProdFactor, wherever Pprod is nonzero *)
Lemma Hseq_eq : forall (rho : nat -> C) (N : nat) (z : C) (H : C -> C),
  (forall w, XiC w = Cmul (H w) (Pprod (fun k => Efac w (rho k)) N)) ->
  Pprod (fun k => Efac z (rho k)) N <> C0 ->
  H z = Hseq rho N z.
Proof.
  intros rho N z H Hid Hne. unfold Hseq. rewrite (Hid z). field. exact Hne.
Qed.

Theorem Hseq_cv : forall (rho : nat -> C),
  ZeroEnum rho -> (forall n, 1 <= Cmod (rho n)) ->
  forall z, (forall n, z <> rho n) ->
  forall P, CUn_cv (Pprod (fun k => Efac z (rho k))) P ->
  CUn_cv (fun N => Hseq rho N z) (Cmul (XiC z) (Cinv P)).
Proof.
  intros rho Henum Hlow z Hz P HP.
  assert (HPne : P <> C0) by (apply (hadamard_prod_ne0 rho Henum Hlow z Hz P HP)).
  assert (Hfne : forall k, Efac z (rho k) <> C0).
  { intro k. apply Efac_ne0; [ | apply Hz ].
    intro Hc. pose proof (Hlow k) as Hl.
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hl. lra. }
  apply CUn_cv_scal.
  apply CUn_cv_inv; [ exact HP | exact HPne | ].
  intro N. apply Pprod_ne0. exact Hfne.
Qed.

Print Assumptions hadamard_prod_ne0.
Print Assumptions Hseq_cv.
