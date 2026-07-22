(* ================================================================= *)
(*  PrimonGas.v                                                       *)
(*                                                                    *)
(*  The FREE RIEMANN GAS (primon gas) and its Euler-product           *)
(*  partition function, over Q, axiom-free.                           *)
(*                                                                    *)
(*  Each prime is a bosonic MODE; an occupation vector k = (k_p) is a  *)
(*  state, with Boltzmann weight  weight(k) = prod_p x_p^{k_p}  where   *)
(*  x_p is the fugacity of mode p (formally x_p = p^{-s}).  The        *)
(*  single-mode partition function is the truncated geometric series   *)
(*  psum x K = sum_{k<K} x^k, and the total partition function is the  *)
(*  sum over ALL occupation states.                                   *)
(*                                                                    *)
(*  MAIN THEOREM (euler_product): the sum over states equals the       *)
(*  PRODUCT over modes of the single-mode partition functions,         *)
(*                                                                    *)
(*     sum_{states} prod_p x_p^{k_p}  =  prod_p ( sum_{k<K} x_p^k ).    *)
(*                                                                    *)
(*  This is the finite Euler product Z = prod_p Z_p: the gas is FREE   *)
(*  (non-interacting) because the modes factorise -- exactly the       *)
(*  independence of primes (coprimality / CRT) from FreeDivMeet.       *)
(*  With x_p = p^{-s} and K -> infinity this is the Euler product for   *)
(*  the Riemann zeta function; the finite identity here is axiom-free. *)
(*                                                                    *)
(*  Also: qpow_add (single-mode energy additivity -> weight            *)
(*  multiplicativity), energy_additive (the log/energy side is         *)
(*  linear), geom_closed (each Z_p is the truncated Euler factor       *)
(*  (1-x^K)/(1-x)), and euler_two_modes (the two-prime / CRT form).    *)
(* ================================================================= *)

From Stdlib Require Import QArith Lqa ZArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  1.  RATIONAL POWERS AND FINITE SUMS/PRODUCTS OVER LISTS           *)
(* ================================================================= *)

Fixpoint qpow (x : Q) (k : nat) : Q :=
  match k with O => 1 | S k' => x * qpow x k' end.

(* single-mode energy adds  ->  Boltzmann weight multiplies *)
Lemma qpow_add : forall x a b, qpow x (a + b) == qpow x a * qpow x b.
Proof.
  intros x a b; induction a as [|a IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

Fixpoint qsum (l : list Q) : Q :=
  match l with [] => 0 | a :: r => a + qsum r end.

Fixpoint qprod (l : list Q) : Q :=
  match l with [] => 1 | a :: r => a * qprod r end.

Lemma qsum_app : forall l1 l2, qsum (l1 ++ l2) == qsum l1 + qsum l2.
Proof.
  induction l1 as [|a l1 IH]; intro l2; simpl; [ ring | rewrite IH; ring ].
Qed.

(* pull a constant out of a finite sum (scalar on the left / right) *)
Lemma qsum_map_scale_l : forall (A : Type) (c : Q) (f : A -> Q) (l : list A),
  qsum (map (fun a => c * f a) l) == c * qsum (map f l).
Proof.
  intros A c f; induction l as [|a l IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

Lemma qsum_map_scale_r : forall (A : Type) (c : Q) (f : A -> Q) (l : list A),
  qsum (map (fun a => f a * c) l) == qsum (map f l) * c.
Proof.
  intros A c f; induction l as [|a l IH]; simpl; [ ring | rewrite IH; ring ].
Qed.

(* rewrite under a finite sum by a pointwise (setoid) equality *)
Lemma qsum_map_ext : forall (A : Type) (f g : A -> Q) (l : list A),
  (forall a, f a == g a) -> qsum (map f l) == qsum (map g l).
Proof.
  intros A f g l H; induction l as [|a l IH]; simpl;
    [ reflexivity | rewrite (H a), IH; reflexivity ].
Qed.

(* a sum over a flat_map is the sum of the per-element sums *)
Lemma qsum_map_flat_map :
  forall (A B : Type) (g : B -> Q) (h : A -> list B) (L : list A),
    qsum (map g (flat_map h L))
    == qsum (map (fun a => qsum (map g (h a))) L).
Proof.
  intros A B g h; induction L as [|a L IH]; simpl;
    [ reflexivity | rewrite map_app, qsum_app, IH; reflexivity ].
Qed.

(* ================================================================= *)
(*  2.  SINGLE-MODE PARTITION FUNCTION (truncated geometric series)   *)
(* ================================================================= *)

Definition psum (x : Q) (K : nat) : Q := qsum (map (qpow x) (seq 0 K)).

Lemma psum_rec : forall x K, psum x (S K) == psum x K + qpow x K.
Proof.
  intros x K; unfold psum.
  rewrite seq_S, map_app, qsum_app; simpl; ring.
Qed.

(* each mode's partition function is the truncated Euler factor:
   (1 - x) * Z_p = 1 - x^K,   so  Z_p = (1 - x^K)/(1 - x) -> 1/(1-x). *)
Theorem geom_closed : forall x K, (1 - x) * psum x K == 1 - qpow x K.
Proof.
  intros x K; induction K as [|K IH].
  - unfold psum; simpl; ring.
  - rewrite psum_rec, Qmult_plus_distr_r, IH.
    change (qpow x (S K)) with (x * qpow x K); ring.
Qed.

(* ================================================================= *)
(*  3.  OCCUPATION STATES AND THE BOLTZMANN WEIGHT                    *)
(* ================================================================= *)

(* Boltzmann weight of an occupation vector ks over modes with        *)
(* fugacities xs:  prod_i x_i^{k_i}                                    *)
Fixpoint weight (xs : list Q) (ks : list nat) : Q :=
  match xs, ks with
  | x :: xs', k :: ks' => qpow x k * weight xs' ks'
  | _, _ => 1
  end.

(* all occupation vectors over the modes xs with each occupation < K *)
Fixpoint gstates (xs : list Q) (K : nat) : list (list nat) :=
  match xs with
  | [] => [ [] ]
  | _ :: xs' => flat_map (fun k => map (cons k) (gstates xs' K)) (seq 0 K)
  end.

(* the inner distributive step: fixing mode 0 at occupation k factors  *)
(* out x^k and leaves the sub-gas partition function                   *)
Lemma inner_factor : forall x xs' K k,
  qsum (map (weight (x :: xs')) (map (cons k) (gstates xs' K)))
  == qpow x k * qsum (map (weight xs') (gstates xs' K)).
Proof.
  intros x xs' K k; rewrite map_map.
  rewrite <- (qsum_map_scale_l (list nat) (qpow x k) (weight xs') (gstates xs' K)).
  apply qsum_map_ext; intro ks; reflexivity.
Qed.

(* ================================================================= *)
(*  4.  THE EULER PRODUCT — sum over states = product over modes      *)
(* ================================================================= *)

Theorem euler_product : forall xs K,
  qsum (map (weight xs) (gstates xs K))
  == qprod (map (fun x => psum x K) xs).
Proof.
  induction xs as [|x xs' IH]; intro K.
  - reflexivity.
  - cbn [gstates].
    rewrite qsum_map_flat_map.
    rewrite (qsum_map_ext nat
               (fun k => qsum (map (weight (x :: xs')) (map (cons k) (gstates xs' K))))
               (fun k => qpow x k * qsum (map (weight xs') (gstates xs' K)))
               (seq 0 K)
               (fun k => inner_factor x xs' K k)).
    rewrite (qsum_map_scale_r nat
               (qsum (map (weight xs') (gstates xs' K))) (qpow x) (seq 0 K)).
    change (qsum (map (qpow x) (seq 0 K))) with (psum x K).
    cbn [qprod map].
    rewrite IH; ring.
Qed.

(* ================================================================= *)
(*  5.  THE ENERGY SIDE IS LINEAR (E(m.n) = E m + E n)                *)
(* ================================================================= *)

Fixpoint ladd (ks ks' : list nat) : list nat :=
  match ks, ks' with
  | k :: r, k' :: r' => (k + k')%nat :: ladd r r'
  | _, _ => nil
  end.

(* energy of an occupation vector: sum_i eps_i * k_i (eps_i the        *)
(* single-particle energy of mode i, e.g. eps_p = log p)              *)
Fixpoint energy (es : list Q) (ks : list nat) : Q :=
  match es, ks with
  | e :: es', k :: ks' => e * inject_Z (Z.of_nat k) + energy es' ks'
  | _, _ => 0
  end.

(* combining states adds occupation -> energies ADD (multiplication of  *)
(* the underlying numbers becomes addition of energies)                *)
Theorem energy_additive : forall es ks ks',
  length ks = length es -> length ks' = length es ->
  energy es (ladd ks ks') == energy es ks + energy es ks'.
Proof.
  induction es as [|e es' IH]; intros ks ks' Hk Hk'.
  - simpl; ring.
  - destruct ks as [|k r]; [ simpl in Hk; discriminate | ].
    destruct ks' as [|k' r']; [ simpl in Hk'; discriminate | ].
    simpl in Hk, Hk'; simpl.
    rewrite IH by lia.
    rewrite Nat2Z.inj_add, inject_Z_plus; ring.
Qed.

(* ================================================================= *)
(*  6.  THE TWO-MODE (CRT) FORM: independent primes factorise         *)
(* ================================================================= *)

(* For two modes (two primes p, q) the partition function factorises   *)
(* into the two single-mode factors -- the primon-gas statement of      *)
(* freeness / coprimality: no cross terms, exactly as gcd(p^a,q^b)=1     *)
(* forces independence in FreeDivMeet.                                 *)
Corollary euler_two_modes : forall x y K,
  qsum (map (weight [x; y]) (gstates [x; y] K)) == psum x K * psum y K.
Proof.
  intros x y K.
  rewrite euler_product; cbn [qprod map]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — axiom-free over Q                               *)
(* ----------------------------------------------------------------- *)

Theorem primon_gas :
  (* the free-gas Euler product: sum over states = product over modes *)
  (forall xs K, qsum (map (weight xs) (gstates xs K))
                == qprod (map (fun x => psum x K) xs))
  (* each mode's partition function is the truncated Euler factor *)
  /\ (forall x K, (1 - x) * psum x K == 1 - qpow x K)
  (* the single-mode energy additivity behind weight multiplicativity *)
  /\ (forall x a b, qpow x (a + b) == qpow x a * qpow x b)
  (* the energy (log) side is linear under state combination *)
  /\ (forall es ks ks', length ks = length es -> length ks' = length es ->
        energy es (ladd ks ks') == energy es ks + energy es ks')
  (* the two-mode / CRT factorisation *)
  /\ (forall x y K, qsum (map (weight [x; y]) (gstates [x; y] K))
                    == psum x K * psum y K).
Proof.
  split; [ exact euler_product | ].
  split; [ exact geom_closed | ].
  split; [ exact qpow_add | ].
  split; [ exact energy_additive | exact euler_two_modes ].
Qed.

Print Assumptions primon_gas.

(* ================================================================= *)
(*  END PrimonGas.v                                                   *)
(*  The free Riemann gas: partition function = sum over occupation     *)
(*  states = product over prime modes (finite Euler product).          *)
(*  Freeness = mode factorisation = coprimality/CRT.                   *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
