(* ================================================================= *)
(*  VonMangoldt.v                                                     *)
(*                                                                    *)
(*  The VON MANGOLDT function and its Mobius inversion, over Q,        *)
(*  axiom-free -- the arithmetic heart behind the logarithmic          *)
(*  derivative of the Euler product.                                  *)
(*                                                                    *)
(*  For a single prime p, index arithmetic functions by the exponent   *)
(*  k (so f(p^k) becomes f k).  With the single-particle energy        *)
(*  L = log p kept as a formal parameter (as in LandauerBoundL):        *)
(*                                                                    *)
(*     Lambda(p^k) = L if k>=1 else 0        (von Mangoldt)            *)
(*     log(p^k)    = k * L                    (logarithm)              *)
(*     mu(p^k)     = 1,-1,0,0,...             (Mobius, from MobiusReciprocal) *)
(*                                                                    *)
(*  The per-prime Dirichlet convolution is the Cauchy product on        *)
(*  exponents.  We prove the two classical identities:                 *)
(*                                                                    *)
(*     Lambda = mu * log           (Mobius inversion)                  *)
(*     sum_{d | p^m} Lambda(d) = log(p^m)   (summatory)                *)
(*                                                                    *)
(*  The first shows mu * (.) is the backward difference operator, so    *)
(*  Lambda is the discrete derivative of log -- the arithmetic mirror   *)
(*  of  -zeta'/zeta = sum_n Lambda(n) n^{-s}  (see VonMangoldtR.v).     *)
(* ================================================================= *)

Require Import MobiusReciprocal.
Require Import PrimonGas.
From Stdlib Require Import QArith Lqa ZArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* a mu-weighted finite sum collapses to its two nonzero terms         *)
(* (generalises MobiusReciprocal.museries_from2 to an arbitrary h).     *)
Lemma mu_weighted : forall (h : nat -> Q) K, (2 <= K)%nat ->
  qsum (map (fun k => inject_Z (mu_pp k) * h k) (seq 0 K)) == h 0%nat - h 1%nat.
Proof.
  intros h K HK.
  destruct K as [|[|n]]; [ exfalso; lia | exfalso; lia | ].
  clear HK; induction n as [|n IH].
  - simpl; unfold mu_pp; simpl.
    replace (inject_Z 1) with 1 by reflexivity.
    replace (inject_Z (-1)) with (-(1)) by reflexivity; ring.
  - rewrite seq_S, map_app, qsum_app, IH; simpl.
    change (mu_pp (S (S n))) with 0%Z.
    replace (inject_Z 0) with 0 by reflexivity; ring.
Qed.

Section VM.

Variable L : Q.   (* the single-prime energy L = log p (formal, as in LandauerBoundL) *)

(* the three arithmetic functions, indexed by the exponent k *)
Definition muf  (j : nat) : Q := inject_Z (mu_pp j).
Definition logf (j : nat) : Q := inject_Z (Z.of_nat j) * L.
Definition lamf (j : nat) : Q := if Nat.eqb j 0 then 0 else L.

(* per-prime Dirichlet convolution: the Cauchy product on exponents *)
Definition dconv (f g : nat -> Q) (n : nat) : Q :=
  qsum (map (fun j => f j * g (n - j)%nat) (seq 0 (S n))).

(* mu * (.) is the BACKWARD DIFFERENCE operator *)
Lemma dconv_mu : forall g n, (1 <= n)%nat ->
  dconv muf g n == g n - g (n - 1)%nat.
Proof.
  intros g n Hn; unfold dconv, muf.
  rewrite (mu_weighted (fun j => g (n - j)%nat) (S n)) by lia.
  rewrite Nat.sub_0_r; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MOBIUS INVERSION:  Lambda = mu * log                             *)
(* ----------------------------------------------------------------- *)

Theorem vm_mobius_inversion : forall m, dconv muf logf m == lamf m.
Proof.
  intros [|m].
  - unfold dconv, muf, logf, lamf; simpl.
    replace (inject_Z 1) with 1 by reflexivity; ring.
  - rewrite dconv_mu by lia; unfold logf, lamf; cbn [Nat.eqb].
    replace (S m - 1)%nat with m by lia.
    replace (Z.of_nat (S m)) with (Z.of_nat m + 1)%Z by lia.
    rewrite inject_Z_plus.
    replace (inject_Z 1) with 1 by reflexivity; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  SUMMATORY:  sum_{d | p^m} Lambda(d) = log(p^m)                   *)
(* ----------------------------------------------------------------- *)

Definition sumf (h : nat -> Q) (m : nat) : Q := qsum (map h (seq 0 (S m))).

Lemma sumf_rec : forall h m, sumf h (S m) == sumf h m + h (S m).
Proof.
  intros h m; unfold sumf.
  rewrite seq_S, map_app, qsum_app; simpl; ring.
Qed.

Theorem vm_summatory : forall m, sumf lamf m == logf m.
Proof.
  induction m as [|m IH].
  - unfold sumf, logf, lamf; simpl; ring.
  - rewrite sumf_rec, IH; unfold logf, lamf; cbn [Nat.eqb].
    replace (Z.of_nat (S m)) with (Z.of_nat m + 1)%Z by lia.
    rewrite inject_Z_plus.
    replace (inject_Z 1) with 1 by reflexivity; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — axiom-free over Q                               *)
(* ----------------------------------------------------------------- *)

Theorem von_mangoldt :
  (* mu * (.) is the backward difference *)
  (forall g n, (1 <= n)%nat -> dconv muf g n == g n - g (n - 1)%nat)
  (* Lambda = mu * log  (Mobius inversion) *)
  /\ (forall m, dconv muf logf m == lamf m)
  (* sum_{d | p^m} Lambda(d) = log(p^m) *)
  /\ (forall m, sumf lamf m == logf m).
Proof.
  split; [ exact dconv_mu | ].
  split; [ exact vm_mobius_inversion | exact vm_summatory ].
Qed.

End VM.

Print Assumptions von_mangoldt.

(* ================================================================= *)
(*  END VonMangoldt.v                                                 *)
(*  Lambda = mu * log (Mobius inversion) and sum_{d|p^m} Lambda = log, *)
(*  per prime power, over Q.  mu * (.) = backward difference, so        *)
(*  Lambda is the discrete derivative of log.                          *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
