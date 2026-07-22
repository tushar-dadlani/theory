(* ================================================================= *)
(*  EulerReindex.v                                                   *)
(*                                                                    *)
(*  REINDEXING THE FINITE EULER PRODUCT ALONG THE code BIJECTION.      *)
(*                                                                    *)
(*  PrimonGas.euler_product already gives the distributive law         *)
(*     sum_{occupation states} weight xs ks  =  prod_modes psum x_i K   *)
(*  and PrimeFactorizationN/Exists give that                           *)
(*     code ps ks = prod_i (ps_i)^(k_i)                                *)
(*  is a BIJECTION of occupation vectors onto {ps}-smooth numbers.      *)
(*                                                                    *)
(*  Here we CONNECT the two: with fugacity  fug p = 1 / (inject_Z p)^2, *)
(*  the primon-gas Boltzmann weight of an occupation vector IS the      *)
(*  reciprocal square of the coded number,                             *)
(*                                                                    *)
(*     weight (map fug ps) ks  =  1 / (inject_Z (code ps ks))^2        *)
(*                             (weight_fug)                            *)
(*                                                                    *)
(*  so the finite Euler product over the primes ps REINDEXES as a sum   *)
(*  of 1/m^2 over the smooth numbers m = code ps ks:                    *)
(*                                                                    *)
(*     prod_i ( sum_{k<K} p_i^{-2k} )                                  *)
(*        =  sum_{occupation states ks} 1 / (code ps ks)^2             *)
(*                             (euler_reindex)                         *)
(*                                                                    *)
(*  and (codes_distinct) these coded numbers are DISTINCT (code is      *)
(*  injective on the occupation states), so the right-hand side is a    *)
(*  sum over distinct {ps}-smooth numbers -- exactly the reindexing      *)
(*  needed to turn the primorial Euler tower into a partial zeta sum.    *)
(*                                                                    *)
(*  Axiom-free over Q: reuses PrimonGas (axiom-free) and                *)
(*  PrimeFactorizationN.code_inj (axiom-free).                         *)
(* ================================================================= *)

Require Import PrimonGas PrimeFactorizationN.
From Stdlib Require Import QArith Lqa ZArith Znumtheory List Lia.
Import ListNotations.
Open Scope Q_scope.

(* qpow respects Qeq in its base -- needed to rewrite under qpow *)
Add Parametric Morphism : qpow
  with signature (Qeq ==> @eq nat ==> Qeq) as qpow_morph.
Proof.
  intros x y Hxy k; induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite IH; setoid_replace x with y by exact Hxy; reflexivity.
Qed.

(* fugacity of a prime p at s = 2 :  p^{-2} = 1/p^2  (as a rational) *)
Definition fug (p : Z) : Q := / qpow (inject_Z p) 2.

(* ----------------------------------------------------------------- *)
(*  qpow / inject_Z homomorphism helpers                             *)
(* ----------------------------------------------------------------- *)

Lemma inj_pow : forall (a : Z) k, inject_Z (a ^ Z.of_nat k) == qpow (inject_Z a) k.
Proof.
  intros a k; induction k as [|k IH]; [ reflexivity | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite inject_Z_mult, IH; simpl; ring.
Qed.

Lemma qpow_mul : forall x y k, qpow (x * y) k == qpow x k * qpow y k.
Proof.
  intros x y k; induction k as [|k IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma qpow_inv : forall x k, qpow (/ x) k == / qpow x k.
Proof.
  intros x k; induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite IH, Qinv_mult_distr; reflexivity.
Qed.

(* q^(a*b) = (q^a)^b *)
Lemma qpow_mult_exp : forall x a b, qpow x (a * b) == qpow (qpow x a) b.
Proof.
  intros x a b; induction b as [|b IH].
  - rewrite Nat.mul_0_r; reflexivity.
  - rewrite Nat.mul_succ_r, qpow_add, IH; simpl; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE KEY IDENTITY: the primon-gas weight is 1/(coded number)^2      *)
(* ----------------------------------------------------------------- *)

Lemma weight_fug : forall ps ks,
  weight (map fug ps) ks == / qpow (inject_Z (code ps ks)) 2.
Proof.
  induction ps as [|p ps' IH]; intro ks.
  - simpl; reflexivity.
  - destruct ks as [|k ks']; [ simpl; reflexivity | ].
    cbn [map weight code].
    rewrite IH.
    (* qpow (fug p) k * / qpow (inject_Z (code ps' ks')) 2
       == / qpow (inject_Z (p^k * code ps' ks')) 2 *)
    unfold fug.
    rewrite qpow_inv.                       (* qpow(/ qpow(inj p)2) k = / qpow(qpow(inj p)2) k *)
    rewrite <- qpow_mult_exp.               (* qpow(qpow(inj p)2) k = qpow(inj p)(2*k) *)
    rewrite inject_Z_mult.                  (* inject_Z(p^k * code) = inject_Z(p^k)*inject_Z(code) *)
    rewrite qpow_mul.                        (* qpow(A*B)2 = qpow A 2 * qpow B 2 *)
    rewrite Qinv_mult_distr.
    rewrite inj_pow.                         (* inject_Z(p^k) == qpow (inject_Z p) k *)
    rewrite <- qpow_mult_exp.               (* qpow(qpow(inj p)k)2 = qpow(inj p)(k*2) *)
    rewrite (Nat.mul_comm k 2).              (* k*2 = 2*k, matching the left factor *)
    reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE REINDEXING: finite Euler product = sum of 1/m^2 over the       *)
(*  occupation-generated smooth numbers                                *)
(* ----------------------------------------------------------------- *)

Theorem euler_reindex : forall ps K,
  qprod (map (fun p => psum (fug p) K) ps)
  == qsum (map (fun ks => / qpow (inject_Z (code ps ks)) 2)
               (gstates (map fug ps) K)).
Proof.
  intros ps K.
  rewrite <- (map_map fug (fun x => psum x K)).
  rewrite <- euler_product.
  apply qsum_map_ext; intro ks; apply weight_fug.
Qed.

(* ----------------------------------------------------------------- *)
(*  DISTINCTNESS: the coded numbers are pairwise distinct             *)
(* ----------------------------------------------------------------- *)

(* every occupation state has length matching the mode list *)
Lemma gstates_length : forall xs K ks,
  In ks (gstates xs K) -> length ks = length xs.
Proof.
  induction xs as [|x xs' IH]; intros K ks Hin.
  - simpl in Hin; destruct Hin as [He | []]; subst; reflexivity.
  - cbn [gstates] in Hin. apply in_flat_map in Hin.
    destruct Hin as [k [_ Hin]]. apply in_map_iff in Hin.
    destruct Hin as [ks0 [Heq Hin0]]; subst ks.
    cbn [length]; f_equal; apply IH with (K := K); exact Hin0.
Qed.

(* code is injective on the occupation states : distinct states code   *)
(* to distinct {ps}-smooth numbers                                     *)
Theorem codes_distinct : forall ps K,
  Forall prime ps -> NoDup ps ->
  forall ks ks',
    In ks  (gstates (map fug ps) K) ->
    In ks' (gstates (map fug ps) K) ->
    code ps ks = code ps ks' -> ks = ks'.
Proof.
  intros ps K Hpr Hnd ks ks' Hin Hin' Hcode.
  assert (Hlks  : length ks  = length ps).
  { rewrite <- (length_map fug ps); apply gstates_length with (K := K); exact Hin. }
  assert (Hlks' : length ks' = length ps).
  { rewrite <- (length_map fug ps); apply gstates_length with (K := K); exact Hin'. }
  apply (code_inj ps ks ks' Hpr Hnd);
    [ symmetry; exact Hlks | symmetry; exact Hlks' | exact Hcode ].
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem euler_product_reindexed : forall ps K,
  Forall prime ps -> NoDup ps ->
  (* the finite Euler product = sum of 1/m^2 over the coded numbers ... *)
  (qprod (map (fun p => psum (fug p) K) ps)
   == qsum (map (fun ks => / qpow (inject_Z (code ps ks)) 2)
                (gstates (map fug ps) K)))
  (* ... which are pairwise distinct {ps}-smooth numbers *)
  /\ (forall ks ks',
        In ks  (gstates (map fug ps) K) ->
        In ks' (gstates (map fug ps) K) ->
        code ps ks = code ps ks' -> ks = ks').
Proof.
  intros ps K Hpr Hnd; split;
    [ apply euler_reindex | apply codes_distinct; assumption ].
Qed.

Print Assumptions euler_product_reindexed.

(* ================================================================= *)
(*  END EulerReindex.v                                               *)
(*  The finite Euler product prod_i (sum_{k<K} p_i^{-2k}) reindexes as  *)
(*  a sum of 1/m^2 over the occupation-generated {ps}-smooth numbers    *)
(*  m = code ps ks, which are pairwise distinct (code injective).       *)
(*  This transports the primon-gas Euler product onto the number line   *)
(*  as a partial zeta sum -- the reindexing half of the deferred crux.  *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
