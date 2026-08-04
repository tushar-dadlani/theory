(* ================================================================= *)
(*  CEulerFactorSmooth.v  —  the FINITE complex Euler-product reindex. *)
(*                                                                    *)
(*  The complex analogue of EulerReindexR.euler_partial_reindex_Rs:    *)
(*  the finite product over p<=N of the truncated geometric series     *)
(*  Σ_{k<K} p^{-ks} equals the sum of m^{-s} over the coded numbers     *)
(*  m = code ps ks (occupation vectors with exponents < K):           *)
(*                                                                    *)
(*    Cwprod (map (fun p => Σ_{k<K} (p^{-s})^k) ps)                    *)
(*      = Cwsum (map (fun ks => (code ps ks)^{-s}) (gstates .. K)).    *)
(*                                                                    *)
(*  Built from DirichletLEuler.euler_product_C (the complex            *)
(*  distributive law) + Cweight_code (the complex weight = coded power,*)
(*  via CPowMul) + statesC_eq_gstates (the occupation enumerations     *)
(*  agree, depending only on list length).  Axiom-clean.              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List QArith.
Require Import ComplexField Cmodulus CexpFull CPowMul RootsOfUnity DirichletLEuler
        PrimonGas PrimeFactorizationN EulerReindex EulerProductZetaBound.
Import ListNotations.
Open Scope R_scope.

(* the occupation-state enumerations agree (they use only list length) *)
Lemma statesC_eq_gstates : forall (xs : list C) (ys : list Q) K,
  length xs = length ys -> statesC xs K = gstates ys K.
Proof.
  induction xs as [|x xs IH]; intros ys K Hlen.
  - destruct ys; [ reflexivity | simpl in Hlen; discriminate ].
  - destruct ys as [|y ys]; [ simpl in Hlen; discriminate | ].
    cbn [statesC gstates]; rewrite (IH ys K ltac:(simpl in Hlen; lia)); reflexivity.
Qed.

(* the complex Boltzmann weight of p^{-s} modes is (code ps ks)^{-s}   *)
(* (mirror of EulerReindexR.Rweight_code)                             *)
Lemma Cweight_code : forall s ps ks,
  Forall prime ps -> length ps = length ks ->
  Cweight (map (fun p => Cpw (IZR p) (Copp s)) ps) ks
  = Cpw (IZR (code ps ks)) (Copp s).
Proof.
  intros s ps; induction ps as [|p ps' IH]; intros ks Hpr Hlen.
  - destruct ks; [ | simpl in Hlen; discriminate ].
    cbn [code map Cweight].
    change (IZR 1) with 1%R; rewrite Cpw_one; reflexivity.
  - destruct ks as [|k ks']; [ simpl in Hlen; discriminate | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    assert (Hpp : (2 <= p)%Z) by (destruct Hp; lia).
    assert (Hp0 : (0 < IZR p)%R) by (apply IZR_lt; lia).
    assert (Hc0 : (0 < IZR (code ps' ks'))%R)
      by (apply IZR_lt; pose proof (code_pos ps' ks' Hpr'); lia).
    assert (Hpk0 : (0 < IZR (p ^ Z.of_nat k))%R)
      by (apply IZR_lt; pose proof (zpow_ge_1 p k ltac:(lia)); lia).
    cbn [map Cweight code].
    rewrite (IH ks' Hpr' ltac:(simpl in Hlen; lia)).
    rewrite mult_IZR.
    rewrite (Cpw_base_mul (IZR (p ^ Z.of_nat k)) (IZR (code ps' ks')) (Copp s) Hpk0 Hc0).
    f_equal.
    rewrite <- pow_IZR.
    rewrite (Cpw_base_pow (IZR p) (Copp s) k Hp0); reflexivity.
Qed.

(* THE FINITE REINDEX: truncated Euler product = sum of coded powers   *)
Theorem Ceuler_reindex_fin : forall s ps K, Forall prime ps ->
  Cwprod (map (fun p => Csum (fun k => Cpow (Cpw (IZR p) (Copp s)) k) K) ps)
  = Cwsum (map (fun ks => Cpw (IZR (code ps ks)) (Copp s)) (gstates (map fug ps) K)).
Proof.
  intros s ps K Hpr.
  rewrite <- (map_map (fun p => Cpw (IZR p) (Copp s))
                      (fun x => Csum (fun k => Cpow x k) K)).
  rewrite <- euler_product_C.
  rewrite (statesC_eq_gstates (map (fun p => Cpw (IZR p) (Copp s)) ps) (map fug ps) K)
    by (rewrite !length_map; reflexivity).
  f_equal; apply map_ext_in; intros ks Hks.
  apply Cweight_code; [ exact Hpr | ].
  symmetry; rewrite <- (length_map fug ps).
  apply (gstates_length (map fug ps) K ks Hks).
Qed.

Print Assumptions Ceuler_reindex_fin.

(* ================================================================= *)
(*  END CEulerFactorSmooth.v                                          *)
(* ================================================================= *)
