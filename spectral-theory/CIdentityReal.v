(* ================================================================= *)
(*  CIdentityReal.v  (identity-theorem plan, B5 + centre shift)        *)
(*                                                                    *)
(*  B5: a holomorphic function vanishing on a real interval has all    *)
(*  its (real-direction = complex) derivatives zero there.             *)
(*                                                                    *)
(*    real_deriv_zero : g = 0 on a real nbhd of c  =>  g'(c) = 0        *)
(*    chain_vanishes_real : a derivative chain whose head vanishes on   *)
(*      a real interval has EVERY member vanishing there.              *)
(*                                                                    *)
(*  Centre shift: combining with CIdentityZero.identity_at_zero on the  *)
(*  translated chain h(z)=f(z+a) gives the identity theorem on a disk   *)
(*  about a real point a where f vanishes on a real interval:          *)
(*                                                                    *)
(*    identity_on_disk : f = 0 on a real nbhd of a  =>  f = 0 on the    *)
(*      whole disk |z-a| < R.                                          *)
(*                                                                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        CDeriv CHoloCalculus CWindingOffCenter CIdentityZero.
Open Scope R_scope.

Lemma Cmod_mkC_real : forall t, Cmod (mkC t 0) = Rabs t.
Proof.
  intro t. unfold Cmod, Cnorm2; cbn [Re Im].
  rewrite Rmult_0_l, Rplus_0_r.
  replace (t * t) with (Rsqr t) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* ---- B5 core: the real-direction derivative vanishes ---- *)
Lemma real_deriv_zero : forall (g gd : C -> C) (c eps : R),
  0 < eps ->
  is_Cderiv g (mkC c 0) (gd (mkC c 0)) ->
  (forall x, Rabs (x - c) < eps -> g (mkC x 0) = C0) ->
  gd (mkC c 0) = C0.
Proof.
  intros g gd c eps Heps Hder Hvan.
  set (d := gd (mkC c 0)) in *.
  assert (Hgc : g (mkC c 0) = C0)
    by (apply Hvan; replace (c - c) with 0 by ring; rewrite Rabs_R0; exact Heps).
  assert (Hall : forall e, 0 < e -> Cmod d <= e).
  { intros e He.
    destruct (Hder e He) as [del [Hdel Hb]].
    set (t := Rmin del eps / 2).
    assert (Ht0 : 0 < t)
      by (unfold t; apply Rmult_lt_0_compat; [ apply Rmin_glb_lt; lra | lra ]).
    assert (Htdel : t < del) by (unfold t; pose proof (Rmin_l del eps); lra).
    assert (Hteps : t < eps) by (unfold t; pose proof (Rmin_r del eps); lra).
    set (h := mkC t 0).
    assert (Hhm : Cmod h = t) by (unfold h; rewrite Cmod_mkC_real, Rabs_right; lra).
    assert (Hhd : Cmod h < del) by (rewrite Hhm; exact Htdel).
    pose proof (Hb h Hhd) as Hbd.
    assert (Hstep : Cadd (mkC c 0) h = mkC (c + t) 0)
      by (unfold h; apply Ceq; simpl; ring).
    assert (Hgct : g (mkC (c + t) 0) = C0)
      by (apply Hvan; replace (c + t - c) with t by ring; rewrite Rabs_right; lra).
    assert (Hdiff : Cminus (Cminus (g (Cadd (mkC c 0) h)) (g (mkC c 0))) (Cmul d h)
                    = Copp (Cmul d h))
      by (rewrite Hstep, Hgct, Hgc; ring).
    rewrite Hdiff, Cmod_opp, Cmod_mul, Hhm in Hbd.
    apply (Rmult_le_reg_r t); [ exact Ht0 | exact Hbd ]. }
  assert (Hd0 : Cmod d <= 0).
  { destruct (Rle_lt_dec (Cmod d) 0) as [Hle | Hpos]; [ exact Hle | ].
    exfalso. pose proof (Hall (Cmod d / 2) ltac:(lra)). lra. }
  pose proof (Cmod_nonneg d).
  apply (proj1 (Cmod0 d)). lra.
Qed.

(* ---- the whole chain vanishes on the interval ---- *)
Lemma chain_vanishes_real : forall (fseq : nat -> C -> C) (a0 eps : R),
  0 < eps ->
  (forall k z, is_Cderiv (fseq k) z (fseq (S k) z)) ->
  (forall x, Rabs (x - a0) < eps -> fseq 0%nat (mkC x 0) = C0) ->
  forall k x, Rabs (x - a0) < eps -> fseq k (mkC x 0) = C0.
Proof.
  intros fseq a0 eps Heps Hchain Hvan0.
  induction k as [|k IH]; intros x Hx.
  - apply Hvan0; exact Hx.
  - apply (real_deriv_zero (fseq k) (fseq (S k)) x (eps - Rabs (x - a0))).
    + lra.
    + apply Hchain.
    + intros x' Hx'. apply IH.
      replace (x' - a0) with ((x' - x) + (x - a0)) by ring.
      eapply Rle_lt_trans; [ apply Rabs_triang | ]. lra.
Qed.

(* ================================================================= *)
(*  Centre shift: identity theorem on a disk about a real point a      *)
(* ================================================================= *)
Theorem identity_on_disk : forall (fseq : nat -> C -> C) (Rr a0 eps : R) (w : C),
  0 < Rr -> 0 < eps ->
  (forall k z, is_Cderiv (fseq k) z (fseq (S k) z)) ->
  (forall k, CcontC (fseq k)) ->
  (forall k, exists Mf, 0 <= Mf /\
     forall u, Cmod (fseq k (Cadd (arc Rr u) (mkC a0 0))) <= Mf) ->
  (forall x, Rabs (x - a0) < eps -> fseq 0%nat (mkC x 0) = C0) ->
  Cmod w < Rr ->
  fseq 0%nat (Cadd w (mkC a0 0)) = C0.
Proof.
  intros fseq Rr a0 eps w HR Heps Hchain Hcc Hbd Hvan0 Hw.
  set (aa := mkC a0 0).
  pose proof (chain_vanishes_real fseq a0 eps Heps Hchain Hvan0) as Hvanall.
  assert (Hres : (fun k z => fseq k (Cadd z aa)) 0%nat w = C0).
  { apply (identity_at_zero Rr (fun k z => fseq k (Cadd z aa)) HR).
    - (* chain *)
      intros k z. cbn beta.
      apply (is_Cderiv_ext (fun ww => fseq k (Cadd (Cmul C1 ww) aa))
                           (fun ww => fseq k (Cadd ww aa)) z (fseq (S k) (Cadd z aa))).
      + intro ww; rewrite Cmul_1_l; reflexivity.
      + replace (fseq (S k) (Cadd z aa))
          with (Cmul C1 (fseq (S k) (Cadd (Cmul C1 z) aa)))
          by (rewrite !Cmul_1_l; reflexivity).
        apply Cderiv_comp_affine. rewrite Cmul_1_l. apply Hchain.
    - (* continuity *)
      intros k gg Hgg. cbn beta.
      apply (Hcc k (fun u => Cadd (gg u) aa)).
      apply Ccont_add; [ exact Hgg | apply Ccont_const ].
    - (* boundedness on the circle *)
      intros k. cbn beta. destruct (Hbd k) as [Mf [HMf HB]].
      exists Mf; split; [ exact HMf | intro u; apply HB ].
    - (* vanishing at 0 *)
      intros k. cbn beta.
      replace (Cadd C0 aa) with aa by ring.
      unfold aa. apply (Hvanall k a0).
      replace (a0 - a0) with 0 by ring; rewrite Rabs_R0; exact Heps.
    - exact Hw. }
  cbn beta in Hres. exact Hres.
Qed.

Print Assumptions real_deriv_zero.
Print Assumptions identity_on_disk.
