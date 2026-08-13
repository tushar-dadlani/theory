(* ================================================================= *)
(*  CIdentityProp.v  (identity-theorem plan, B6 propagation)           *)
(*                                                                    *)
(*  Propagation of vanishing across the domain.  For a holomorphic     *)
(*  derivative chain fseq (globally, with circle bounds), if ALL       *)
(*  derivatives vanish at a single point p, then fseq 0 vanishes        *)
(*  everywhere -- by filling the disk about p and stepping along the    *)
(*  segment to any target w.                                           *)
(*                                                                    *)
(*    deriv_zero_on_open  : g=0 on a complex nbhd of p => g'(p)=0       *)
(*    identity_disk_at    : all derivs 0 at p => fseq 0 = 0 on D(p,R)   *)
(*    chain_vanishes_disk : all derivs 0 at p => all derivs 0 on D(p,R) *)
(*    propagate_step      : all derivs 0 at p, |q-p|<R => all 0 at q    *)
(*    identity_propagate  : all derivs 0 at p => fseq 0 w = 0 (any w)   *)
(*                                                                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        CDeriv CHoloCalculus CWindingOffCenter CIdentityZero CIdentityReal.
Open Scope R_scope.

(* g vanishing on a complex neighbourhood of p has zero derivative there *)
Lemma deriv_zero_on_open : forall (g gd : C -> C) (p : C) (eps : R),
  0 < eps ->
  is_Cderiv g p (gd p) ->
  (forall z, Cmod (Cminus z p) < eps -> g z = C0) ->
  gd p = C0.
Proof.
  intros g gd p eps Heps Hder Hvan.
  set (d := gd p) in *.
  assert (Hgp : g p = C0)
    by (apply Hvan; replace (Cminus p p) with C0 by ring;
        rewrite (proj2 (Cmod0 C0) eq_refl); exact Heps).
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
    assert (Hin : g (Cadd p h) = C0).
    { apply Hvan. replace (Cminus (Cadd p h) p) with h by ring. rewrite Hhm; exact Hteps. }
    assert (Hdiff : Cminus (Cminus (g (Cadd p h)) (g p)) (Cmul d h) = Copp (Cmul d h))
      by (rewrite Hin, Hgp; ring).
    rewrite Hdiff, Cmod_opp, Cmod_mul, Hhm in Hbd.
    apply (Rmult_le_reg_r t); [ exact Ht0 | exact Hbd ]. }
  assert (Hd0 : Cmod d <= 0).
  { destruct (Rle_lt_dec (Cmod d) 0) as [Hle | Hpos]; [ exact Hle | ].
    exfalso. pose proof (Hall (Cmod d / 2) ltac:(lra)). lra. }
  pose proof (Cmod_nonneg d). apply (proj1 (Cmod0 d)). lra.
Qed.

Lemma exists_nat_gt : forall r, 0 <= r -> exists n : nat, r < INR n.
Proof.
  intros r Hr. destruct (archimed r) as [Hup _].
  assert (Hpos : (0 < up r)%Z) by (apply lt_IZR; simpl; lra).
  exists (Z.to_nat (up r)).
  rewrite INR_IZR_INZ, Z2Nat.id by lia. exact Hup.
Qed.

Section Propagate.
Variable Rr : R.
Variable fseq : nat -> C -> C.
Hypothesis HR : 0 < Rr.
Hypothesis Hchain : forall k z, is_Cderiv (fseq k) z (fseq (S k) z).
Hypothesis Hcc : forall k, CcontC (fseq k).
Hypothesis Hbd : forall p k, exists Mf, 0 <= Mf /\
  forall u, Cmod (fseq k (Cadd (arc Rr u) p)) <= Mf.

(* all derivatives vanish at p  =>  fseq 0 vanishes on the disk about p *)
Lemma identity_disk_at : forall p w,
  (forall k, fseq k p = C0) -> Cmod w < Rr -> fseq 0 (Cadd w p) = C0.
Proof.
  intros p w Hp Hw.
  assert (Hres : (fun k z => fseq k (Cadd z p)) 0%nat w = C0).
  { apply (identity_at_zero Rr (fun k z => fseq k (Cadd z p)) HR).
    - intros k z. cbn beta.
      apply (is_Cderiv_ext (fun ww => fseq k (Cadd (Cmul C1 ww) p))
                           (fun ww => fseq k (Cadd ww p)) z (fseq (S k) (Cadd z p))).
      + intro ww; rewrite Cmul_1_l; reflexivity.
      + replace (fseq (S k) (Cadd z p))
          with (Cmul C1 (fseq (S k) (Cadd (Cmul C1 z) p)))
          by (rewrite !Cmul_1_l; reflexivity).
        apply Cderiv_comp_affine. rewrite Cmul_1_l. apply Hchain.
    - intros k gg Hgg. cbn beta.
      apply (Hcc k (fun u => Cadd (gg u) p)).
      apply Ccont_add; [ exact Hgg | apply Ccont_const ].
    - intros k. cbn beta. destruct (Hbd p k) as [Mf [HMf HB]].
      exists Mf; split; [ exact HMf | intro u; apply HB ].
    - intros k. cbn beta. replace (Cadd C0 p) with p by ring. apply Hp.
    - exact Hw. }
  cbn beta in Hres. exact Hres.
Qed.

(* ... and hence all derivatives vanish on that disk *)
Lemma chain_vanishes_disk : forall p,
  (forall k, fseq k p = C0) ->
  forall k z, Cmod (Cminus z p) < Rr -> fseq k z = C0.
Proof.
  intros p Hp k. induction k as [|k IH]; intros z Hz.
  - (* base: fseq 0 z = 0 on the disk, from identity_disk_at with w = z - p *)
    replace z with (Cadd (Cminus z p) p) by ring.
    apply identity_disk_at; [ exact Hp | ].
    replace (Cminus z p) with (Cminus z p) by reflexivity. exact Hz.
  - (* step: derivative of a locally-zero function is zero *)
    apply (deriv_zero_on_open (fseq k) (fseq (S k)) z (Rr - Cmod (Cminus z p))).
    + lra.
    + apply Hchain.
    + intros z' Hz'. apply IH.
      (* |z' - p| <= |z' - z| + |z - p| < (Rr - |z-p|) + |z-p| = Rr *)
      replace (Cminus z' p) with (Cadd (Cminus z' z) (Cminus z p)) by ring.
      eapply Rle_lt_trans; [ apply Cmod_triangle | ]. lra.
Qed.

(* one step of propagation *)
Lemma propagate_step : forall p q,
  (forall k, fseq k p = C0) -> Cmod (Cminus q p) < Rr ->
  forall k, fseq k q = C0.
Proof.
  intros p q Hp Hq k. apply (chain_vanishes_disk p Hp k q Hq).
Qed.

(* propagate along the segment from p to w in N equal steps *)
Lemma seg_all_vanish : forall (p w : C) (N : nat), (0 < N)%nat ->
  (forall k, fseq k p = C0) ->
  Cmod (Cminus w p) / INR N < Rr ->
  forall i, (i <= N)%nat ->
  forall k, fseq k (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p))) = C0.
Proof.
  intros p w N HN Hp Hstep i.
  assert (HNr : 0 < INR N) by (apply lt_0_INR; lia).
  induction i as [|i IH]; intros Hi k.
  - replace (Cadd p (Cmul (RtoC (INR 0 * / INR N)) (Cminus w p))) with p.
    2:{ replace (INR 0 * / INR N) with 0 by (simpl; ring).
        change (RtoC 0) with C0. ring. }
    apply Hp.
  - apply (propagate_step
             (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p)))
             (Cadd p (Cmul (RtoC (INR (S i) * / INR N)) (Cminus w p)))).
    + apply IH; lia.
    + replace (Cminus (Cadd p (Cmul (RtoC (INR (S i) * / INR N)) (Cminus w p)))
                      (Cadd p (Cmul (RtoC (INR i * / INR N)) (Cminus w p))))
        with (Cmul (Cminus (RtoC (INR (S i) * / INR N)) (RtoC (INR i * / INR N)))
                   (Cminus w p)) by ring.
      replace (Cminus (RtoC (INR (S i) * / INR N)) (RtoC (INR i * / INR N)))
        with (RtoC (/ INR N)).
      2:{ apply Ceq; unfold RtoC, Cminus; cbn [Re Im].
          - rewrite S_INR; field; lra.
          - ring. }
      rewrite Cmod_mul, Cmod_RtoC, Rabs_right by (left; apply Rinv_0_lt_compat; exact HNr).
      unfold Rdiv in Hstep. rewrite Rmult_comm. exact Hstep.
Qed.

Theorem identity_propagate : forall p w,
  (forall k, fseq k p = C0) -> fseq 0 w = C0.
Proof.
  intros p w Hp.
  destruct (exists_nat_gt (Cmod (Cminus w p) / Rr)
              ltac:(apply Rle_mult_inv_pos; [ apply Cmod_nonneg | exact HR ])) as [N HNgt].
  set (N' := S N).
  assert (HN' : (0 < N')%nat) by lia.
  assert (HNr' : 0 < INR N') by (apply lt_0_INR; lia).
  assert (HNge : Cmod (Cminus w p) / Rr < INR N').
  { unfold N'. rewrite S_INR. lra. }
  assert (Hstep : Cmod (Cminus w p) / INR N' < Rr).
  { apply (Rmult_lt_reg_r (INR N')); [ exact HNr' | ].
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
    apply (Rmult_lt_reg_r (/ Rr)); [ apply Rinv_0_lt_compat; exact HR | ].
    replace (Rr * INR N' * / Rr) with (INR N') by (field; lra).
    unfold Rdiv in HNge. exact HNge. }
  pose proof (seg_all_vanish p w N' HN' Hp Hstep N' (le_n N') 0%nat) as Hend.
  replace (Cadd p (Cmul (RtoC (INR N' * / INR N')) (Cminus w p))) with w in Hend.
  2:{ replace (INR N' * / INR N') with 1 by (field; lra).
      change (RtoC 1) with C1. ring. }
  exact Hend.
Qed.

End Propagate.

Print Assumptions deriv_zero_on_open.
Print Assumptions identity_propagate.
