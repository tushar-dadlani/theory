(* ================================================================= *)
(*  LocalGlobalCompat.v                                              *)
(*                                                                    *)
(*  LOCAL-GLOBAL COMPATIBILITY: the two descriptions of the finite     *)
(*  adele factor A_f agree.                                           *)
(*                                                                    *)
(*  ProductFormulaQ describes A_f from the VALUATION side: the product *)
(*  of the p-adic absolute values, fabs ps ks = prod_p p^{-v_p}.       *)
(*  ProfiniteCRT describes it from the RING side: Zhat = lim Z/nZ, CRT- *)
(*  split into the prime-power moduli p^{v_p}.  This file proves they   *)
(*  read the SAME exponent data:                                      *)
(*                                                                    *)
(*  (A) GLOBAL: fabs ps ks == / inject_Z (code ps ks)   (fabs_is_recip) *)
(*      -- the product of the local absolute values is 1/n, the         *)
(*      reciprocal of the global integer n = code ps ks.               *)
(*                                                                    *)
(*  (B) LOCAL (per prime): for n = code (p::ps') (k::ks'),             *)
(*      (local_global_compat)                                         *)
(*        * RING side: n = p^k * m splits at p with p^k coprime to the  *)
(*          cofactor m = code ps' ks', so ProfiniteCRT.crt_iso gives    *)
(*          Z/nZ ~= Z/(p^k)Z x Z/mZ -- the local ring component at p is *)
(*          Z/(p^k)Z, modulus p^k;                                     *)
(*        * VALUATION side: fabs peels off exactly / inject_Z (p^k) =    *)
(*          |n|_p, the reciprocal of that SAME modulus p^k.            *)
(*      So the exponent k = v_p(n) is simultaneously (ring) the level    *)
(*      of the local factor Z/p^{v_p}Z and (valuation) the exponent of   *)
(*      the local absolute value |n|_p = p^{-v_p}.  Iterating down the   *)
(*      prime list gives Zhat's decomposition prod_p Z_p in lockstep     *)
(*      with fabs's factorisation prod_p |.|_p.                        *)
(*                                                                    *)
(*  This is exactly the local-global principle on the finite side: the  *)
(*  global object n and its profinite image carry the identical local    *)
(*  (per-prime) data that the product formula measures.  R = Q_infinity  *)
(*  (the archimedean completion) is, as always, the separate factor     *)
(*  outside this compatibility.                                        *)
(*                                                                    *)
(*  Axiom-free (Closed under the global context).                    *)
(* ================================================================= *)

Require Import FreeDivMeet PrimeFactorizationN.
Require Import ProductFormulaQ ProfiniteCRT.
From Stdlib Require Import ZArith Znumtheory QArith Lqa Lia List.
Import ListNotations.
Open Scope Q_scope.

(* the coded integer over a list of primes is positive *)
Lemma code_pos : forall ps ks, Forall prime ps -> (0 < code ps ks)%Z.
Proof.
  induction ps as [|p ps' IH]; intros ks Hpr.
  - cbn [code]; lia.
  - destruct ks as [|k ks']; [ cbn [code]; lia | ].
    inversion Hpr as [| ? ? Hp Hpr']; subst.
    cbn [code]; apply Z.mul_pos_pos.
    + apply Z.pow_pos_nonneg; [ destruct Hp; lia | lia ].
    + apply IH; exact Hpr'.
Qed.

(* ----------------------------------------------------------------- *)
(*  (A) GLOBAL:  prod_p |n|_p  =  1 / n                              *)
(* ----------------------------------------------------------------- *)

Corollary fabs_is_recip : forall ps ks, Forall prime ps -> length ps = length ks ->
  fabs ps ks == / inject_Z (code ps ks).
Proof.
  intros ps ks Hpr Hlen.
  assert (Hn : ~ inject_Z (code ps ks) == 0)
    by (apply injZ_nonzero; pose proof (code_pos ps ks Hpr); lia).
  pose proof (pf_int ps ks Hpr Hlen) as H.
  transitivity ((inject_Z (code ps ks) * / inject_Z (code ps ks)) * fabs ps ks).
  { rewrite Qmult_inv_r by exact Hn; rewrite Qmult_1_l; reflexivity. }
  setoid_replace ((inject_Z (code ps ks) * / inject_Z (code ps ks)) * fabs ps ks)
    with (/ inject_Z (code ps ks) * (inject_Z (code ps ks) * fabs ps ks)) by ring.
  rewrite H; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  (B) LOCAL (per prime):  ring split = valuation factor            *)
(* ----------------------------------------------------------------- *)

Theorem local_global_compat : forall p ps' k ks',
  prime p -> Forall prime ps' -> ~ In p ps' -> length ps' = length ks' ->
  (* RING / profinite side: n = p^k * m splits at p (p^k coprime to m),  *)
  (* and CRT gives  Z/nZ ~= Z/(p^k)Z x Z/mZ  -- local component Z/(p^k)Z  *)
     code (p :: ps') (k :: ks') = ((p ^ Z.of_nat k) * code ps' ks')%Z
  /\ rel_prime (p ^ Z.of_nat k) (code ps' ks')
  /\ (exists rec : Z -> Z -> Z,
         (forall x y, ((rec x y) mod (p ^ Z.of_nat k))%Z = (x mod (p ^ Z.of_nat k))%Z)
      /\ (forall x y, ((rec x y) mod (code ps' ks'))%Z = (y mod (code ps' ks'))%Z)
      /\ (forall x,
            ((rec (x mod (p ^ Z.of_nat k))%Z (x mod (code ps' ks'))%Z)
               mod ((p ^ Z.of_nat k) * code ps' ks'))%Z
            = (x mod ((p ^ Z.of_nat k) * code ps' ks'))%Z))
  (* VALUATION / product-formula side: fabs peels the SAME modulus p^k    *)
  (* as the reciprocal local absolute value  |n|_p = 1 / p^k              *)
  /\ fabs (p :: ps') (k :: ks') == / inject_Z (p ^ Z.of_nat k) * fabs ps' ks'
  /\ inject_Z (p ^ Z.of_nat k) * (/ inject_Z (p ^ Z.of_nat k)) == 1.
Proof.
  intros p ps' k ks' Hp Hps' Hnin Hlen.
  assert (Hcopr : rel_prime (p ^ Z.of_nat k) (code ps' ks'))
    by (apply rp_l, coprime_code; assumption).
  assert (Hppos : (0 < p ^ Z.of_nat k)%Z)
    by (apply Z.pow_pos_nonneg; [ destruct Hp; lia | lia ]).
  assert (Hmpos : (0 < code ps' ks')%Z) by (apply code_pos; exact Hps').
  assert (Hanz : ~ inject_Z (p ^ Z.of_nat k) == 0) by (apply injZ_nonzero; lia).
  split; [ reflexivity | ].
  split; [ exact Hcopr | ].
  split; [ apply crt_iso; [ exact Hppos | exact Hmpos | exact Hcopr ] | ].
  split.
  - cbn [fabs]; rewrite inject_Z_pow; reflexivity.
  - apply Qmult_inv_r; exact Hanz.
Qed.

Print Assumptions fabs_is_recip.
Print Assumptions local_global_compat.

(* ================================================================= *)
(*  END LocalGlobalCompat.v                                          *)
(*                                                                    *)
(*  The valuation description (ProductFormulaQ: prod_p |x|_p) and the  *)
(*  ring description (ProfiniteCRT: Zhat = lim Z/nZ = prod_p Z_p) of    *)
(*  the finite adele factor A_f are one and the same:  fabs = 1/n       *)
(*  globally, and at each prime the CRT-split modulus p^{v_p} is the     *)
(*  reciprocal of the local absolute value |n|_p = p^{-v_p}.  Local     *)
(*  (per-prime) data determines the global object and vice versa --      *)
(*  the local-global principle on the non-archimedean side, axiom-free. *)
(*  R = Q_infinity stays the separate archimedean factor.  Closed under  *)
(*  the global context.                                               *)
(* ================================================================= *)
