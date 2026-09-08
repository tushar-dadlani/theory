(* ================================================================= *)
(*  CEulerReindexGen.v  --  the finite Euler reindex, for ANY          *)
(*  completely multiplicative coefficient.                            *)
(*                                                                    *)
(*  CEulerFactorSmooth.Ceuler_reindex_fin proves                       *)
(*                                                                    *)
(*    prod_p (sum_{k<K} (p^{-s})^k) = sum_{ks} (code ps ks)^{-s}       *)
(*                                                                    *)
(*  and its crux Cweight_code uses exactly two facts about the         *)
(*  coefficient m |-> m^{-s}: Cpw_base_mul and Cpw_base_pow.  Both are *)
(*  instances of complete multiplicativity, so the whole thing goes    *)
(*  through for an abstract F : Z -> C with                            *)
(*                                                                    *)
(*    F 1 = 1     and     F (u v) = F u * F v   for u, v > 0.          *)
(*                                                                    *)
(*  euler_product_C (the distributive law) and statesC_eq_gstates      *)
(*  are already generic in an arbitrary list C, so only Cweight has    *)
(*  to be re-proved -- and it SHRINKS, because F (p^k) = (F p)^k       *)
(*  becomes a short induction instead of a Cpw_base_pow appeal.        *)
(*                                                                    *)
(*  Instantiating F p := p^{-s} recovers the original; instantiating   *)
(*  F p := chi(p) p^{-s} gives the Dirichlet L-function twist.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia ZArith Znumtheory List QArith.
Require Import ComplexField Cmodulus CexpFull CPowMul RootsOfUnity DirichletLEuler
        PrimonGas PrimeFactorizationN EulerReindex EulerProductZetaBound
        CEulerFactorSmooth.
Import ListNotations.
Open Scope R_scope.

Section Gen.

Variable F : Z -> C.
Hypothesis F1 : F 1%Z = C1.
Hypothesis Fmul : forall u v, (0 < u)%Z -> (0 < v)%Z ->
  F (u * v)%Z = Cmul (F u) (F v).

(* complete multiplicativity gives the power rule *)
Lemma F_pow_gen : forall c k, (0 < c)%Z -> F (c ^ Z.of_nat k)%Z = Cpow (F c) k.
Proof.
  intros c k Hc. induction k as [| k IH]; cbn [Cpow].
  - rewrite Z.pow_0_r. exact F1.
  - assert (Hck : (0 < c ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite (Fmul c (c ^ Z.of_nat k)%Z Hc Hck), IH. reflexivity.
Qed.

(* the Boltzmann weight of the F-fugacities is F of the coded number *)
Lemma Cweight_gen : forall ps ks,
  Forall prime ps -> length ps = length ks ->
  Cweight (map F ps) ks = F (code ps ks).
Proof.
  induction ps as [| p ps' IH]; intros ks Hpr Hlen.
  - destruct ks; [ | simpl in Hlen; discriminate ].
    cbn [code map Cweight]. symmetry; exact F1.
  - destruct ks as [| k ks']; [ simpl in Hlen; discriminate | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    assert (Hpp : (2 <= p)%Z) by (destruct Hp; lia).
    assert (Hpk : (0 < p ^ Z.of_nat k)%Z)
      by (pose proof (zpow_ge_1 p k ltac:(lia)); lia).
    assert (Hc : (0 < code ps' ks')%Z)
      by (pose proof (code_pos ps' ks' Hpr'); lia).
    cbn [map Cweight code].
    rewrite (IH ks' Hpr' ltac:(simpl in Hlen; lia)).
    rewrite (Fmul (p ^ Z.of_nat k)%Z (code ps' ks') Hpk Hc).
    f_equal. symmetry. apply F_pow_gen. lia.
Qed.

(* THE FINITE REINDEX, for an arbitrary completely multiplicative F *)
Theorem Ceuler_reindex_gen : forall ps K, Forall prime ps ->
  Cwprod (map (fun p => Csum (fun k => Cpow (F p) k) K) ps)
  = Cwsum (map (fun ks => F (code ps ks)) (gstates (map fug ps) K)).
Proof.
  intros ps K Hpr.
  rewrite <- (map_map F (fun x => Csum (fun k => Cpow x k) K)).
  rewrite <- euler_product_C.
  rewrite (statesC_eq_gstates (map F ps) (map fug ps) K)
    by (rewrite !length_map; reflexivity).
  f_equal; apply map_ext_in; intros ks Hks.
  apply Cweight_gen; [ exact Hpr | ].
  symmetry; rewrite <- (length_map fug ps).
  apply (gstates_length (map fug ps) K ks Hks).
Qed.

End Gen.

Print Assumptions Ceuler_reindex_gen.

(* ================================================================= *)
(*  END CEulerReindexGen.v                                            *)
(* ================================================================= *)
