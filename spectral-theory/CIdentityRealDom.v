(* ================================================================= *)
(*  CIdentityRealDom.v  (identity-theorem plan, DOMAIN-RESTRICTED B5)   *)
(*                                                                    *)
(*  chain_vanishes_real_D + identity_on_disk_D for a derivative chain   *)
(*  differentiable only on the disk |z - a| < R+1 and pointwise-        *)
(*  continuous everywhere.  Same as CIdentityReal, with the global      *)
(*  chain hypothesis restricted and identity_at_zero -> _D.            *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral Holomorphic
        CDeriv CWindingOffCenter CIdentityReal CIdentityZeroDom.
Open Scope R_scope.

(* the chain's head vanishes on the interval => every member does *)
Lemma chain_vanishes_real_D : forall (fseq : nat -> C -> C) (a0 eps : R),
  0 < eps ->
  (forall k x, Rabs (x - a0) < eps ->
     is_Cderiv (fseq k) (mkC x 0) (fseq (S k) (mkC x 0))) ->
  (forall x, Rabs (x - a0) < eps -> fseq 0%nat (mkC x 0) = C0) ->
  forall k x, Rabs (x - a0) < eps -> fseq k (mkC x 0) = C0.
Proof.
  intros fseq a0 eps Heps Hchain_int Hvan0.
  induction k as [|k IH]; intros x Hx.
  - apply Hvan0; exact Hx.
  - apply (real_deriv_zero (fseq k) (fseq (S k)) x (eps - Rabs (x - a0))).
    + lra.
    + exact (Hchain_int k x Hx).
    + intros x' Hx'. apply IH.
      replace (x' - a0) with ((x' - x) + (x - a0)) by ring.
      eapply Rle_lt_trans; [ apply Rabs_triang | ]. lra.
Qed.

(* ---- centre shift: identity theorem on a disk about a real point ---- *)
Theorem identity_on_disk_D : forall (fseq : nat -> C -> C) (Rr a0 eps : R) (w : C),
  0 < Rr -> 0 < eps -> eps <= Rr + 1 ->
  (forall k z, Cmod (Cminus z (mkC a0 0)) < Rr + 1 ->
     is_Cderiv (fseq k) z (fseq (S k) z)) ->
  (forall k z e, 0 < e -> exists del, 0 < del /\
     forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (fseq k z') (fseq k z)) < e) ->
  (forall k, exists Mf, 0 <= Mf /\
     forall u, Cmod (fseq k (Cadd (arc Rr u) (mkC a0 0))) <= Mf) ->
  (forall x, Rabs (x - a0) < eps -> fseq 0%nat (mkC x 0) = C0) ->
  Cmod w < Rr ->
  fseq 0%nat (Cadd w (mkC a0 0)) = C0.
Proof.
  intros fseq Rr a0 eps w HR Heps Heps1 Hchain_disk Fptc Hbd Hvan0 Hw.
  set (aa := mkC a0 0).
  (* the real interval sits inside the disk about aa, so the chain
     differentiates there; chain_vanishes_real_D gives all levels vanish *)
  assert (Hchain_int : forall k x, Rabs (x - a0) < eps ->
            is_Cderiv (fseq k) (mkC x 0) (fseq (S k) (mkC x 0))).
  { intros k x Hx. apply Hchain_disk.
    replace (Cminus (mkC x 0) (mkC a0 0)) with (mkC (x - a0) 0)
      by (apply Ceq; simpl; ring).
    rewrite Cmod_mkC_real. lra. }
  pose proof (chain_vanishes_real_D fseq a0 eps Heps Hchain_int Hvan0) as Hvanall.
  assert (Hres : (fun k z => fseq k (Cadd z aa)) 0%nat w = C0).
  { apply (identity_at_zero_D Rr (fun k z => fseq k (Cadd z aa)) HR).
    - (* chain, disk-restricted *)
      intros k z Hzd. cbn beta.
      apply (is_Cderiv_ext (fun ww => fseq k (Cadd (Cmul C1 ww) aa))
                           (fun ww => fseq k (Cadd ww aa)) z (fseq (S k) (Cadd z aa))).
      + intro ww; rewrite Cmul_1_l; reflexivity.
      + replace (fseq (S k) (Cadd z aa))
          with (Cmul C1 (fseq (S k) (Cadd (Cmul C1 z) aa)))
          by (rewrite !Cmul_1_l; reflexivity).
        apply Cderiv_comp_affine. rewrite Cmul_1_l.
        apply Hchain_disk.
        replace (Cminus (Cadd z aa) (mkC a0 0)) with z by (unfold aa; ring). exact Hzd.
    - (* pointwise continuity of the shifted chain *)
      intros k z e He. cbn beta.
      destruct (Fptc k (Cadd z aa) e He) as [del [Hdel Hb]].
      exists del; split; [ exact Hdel | ].
      intros z' Hz'. apply (Hb (Cadd z' aa)).
      replace (Cminus (Cadd z' aa) (Cadd z aa)) with (Cminus z' z) by ring. exact Hz'.
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

Print Assumptions identity_on_disk_D.
