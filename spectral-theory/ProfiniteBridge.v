(* ================================================================= *)
(*  ProfiniteBridge.v                                                *)
(*                                                                    *)
(*  BRIDGES tying the three faces of "(primorial)^oo" together:        *)
(*                                                                    *)
(*   Phi   : InvLim -> Zp p   -- the ORDER (omega+1) tower maps into    *)
(*           the p-adic RING tower by  n |-> p^(exponent at level n).   *)
(*           This is the load-bearing new proof: the min-truncation     *)
(*           bonding map of the order tower matches the mod-p^n bonding  *)
(*           map of the ring tower.  Its top infty maps to p^oo = 0.     *)
(*                                                                    *)
(*   compW : Zhat -> Zp p     -- the profinite integer Zhat = lim Z/n!Z  *)
(*           projects to each p-adic component Z_p (the ring face        *)
(*           factors as prod_p Z_p, cf. ProfiniteCRT.crt_iso).          *)
(*                                                                    *)
(*  Axiom-free (nat only).                                            *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia Factorial.
Require Import PadicIntegers InvLimit ChainTower ProfiniteInteger EuclidPrimes.

(* ----------------------------------------------------------------- *)
(*  Generic modulus helpers                                          *)
(* ----------------------------------------------------------------- *)

(* reducing mod m then mod a divisor d of m is the same as mod d *)
Lemma mod_mod_div : forall d m y, Nat.divide d m -> (y mod m) mod d = y mod d.
Proof.
  intros d m y [q ->]. rewrite (Nat.mul_comm q d).
  rewrite Nat.Div0.mod_mul_r, (Nat.mul_comm d), Nat.Div0.mod_add, Nat.Div0.mod_mod.
  reflexivity.
Qed.

(* the factorial tower is monotone in divisibility: n <= N -> n! | N! *)
Lemma M_div : forall n N, n <= N -> Nat.divide (M n) (M N).
Proof.
  intros n N; induction N as [| N IH]; intro Hn.
  - assert (n = 0) by lia; subst n; apply Nat.divide_refl.
  - destruct (Nat.eq_dec n (S N)) as [-> | Hne]; [ apply Nat.divide_refl | ].
    apply (Nat.divide_trans (M n) (M N)); [ apply IH; lia | ].
    rewrite M_succ; exists (S N); ring.
Qed.

(* ================================================================= *)
(*  Phi : InvLim -> Zp p                                             *)
(* ================================================================= *)

Definition Phidig (p : nat) (X : InvLim) (n : nat) : nat :=
  p ^ (val (projL n X)) mod p ^ n.

Lemma Phi_coh : forall p (Hp : 2 <= p) X, redcoh p (Phidig p X).
Proof.
  intros p Hp X n. unfold Phidig.
  rewrite (PadicIntegers.nested_mod p (p ^ (val (projL (S n) X))) n).
  (* goal: p^(val(projL n X)) mod p^n = p^(val(projL(S n) X)) mod p^n *)
  assert (Hmin : Nat.min (val (projL (S n) X)) n = val (projL n X))
    by (exact (projL_cone X n)).
  destruct (Nat.min_spec (val (projL (S n) X)) n) as [[Hle Heq] | [Hgt Heq]].
  - rewrite <- Hmin, Heq; reflexivity.
  - rewrite <- Hmin, Heq. rewrite Nat.Div0.mod_same. symmetry.
    replace (val (projL (S n) X)) with (n + (val (projL (S n) X) - n)) by lia.
    rewrite Nat.pow_add_r, (Nat.mul_comm (p ^ n)), Nat.Div0.mod_mul; reflexivity.
Qed.

Definition Phi (p : nat) (Hp : 2 <= p) (X : InvLim) : Zp p :=
  exist (redcoh p) (Phidig p X) (Phi_coh p Hp X).

Lemma Phi_proj : forall p Hp X n,
  projZ p n (Phi p Hp X) = p ^ (val (projL n X)) mod p ^ n.
Proof. reflexivity. Qed.

(* the order-top infty maps to p^oo = 0 in every Z_p *)
Lemma Phi_infty : forall p (Hp : 2 <= p) n,
  projZ p n (Phi p Hp infty) = projZ p n (Zzero p).
Proof.
  intros p Hp n. rewrite Phi_proj.
  change (val (projL n infty)) with n. rewrite Nat.Div0.mod_same. reflexivity.
Qed.

(* a natural m maps to the p-adic p^m (capped by the level) *)
Lemma Phi_emb : forall p (Hp : 2 <= p) m n,
  projZ p n (Phi p Hp (emb m)) = p ^ (Nat.min m n) mod p ^ n.
Proof. intros p Hp m n. rewrite Phi_proj. reflexivity. Qed.

(* ================================================================= *)
(*  compW : Zhat -> Zp p                                             *)
(* ================================================================= *)

(* p^k divides (p^k)! = M (p^k) -- p^k is literally one of its factors *)
Lemma ppow_div_M : forall p k, 2 <= p -> Nat.divide (p ^ k) (M (p ^ k)).
Proof.
  intros p k Hp. unfold M. apply divide_fact.
  assert (p ^ k <> 0) by (apply Nat.pow_nonzero; lia).
  split; [ lia | apply Nat.le_refl ].
Qed.

(* iterated coherence of Zhat: read at any higher level, reduce back *)
Lemma projW_gap : forall d X n, digitsW X (n + d) mod (M n) = digitsW X n.
Proof.
  induction d as [| d IH]; intros X n.
  - rewrite Nat.add_0_r.
    (* digitsW X n < M n, so mod is identity *)
    pose proof (projW_cone X n) as Hc; unfold projW in Hc.
    rewrite Hc at 1. rewrite Nat.Div0.mod_mod. rewrite <- Hc; reflexivity.
  - replace (n + S d) with (S (n + d)) by lia.
    pose proof (projW_cone X (n + d)) as Hc; unfold projW in Hc.
    rewrite <- (IH X n). rewrite Hc.
    rewrite (mod_mod_div (M n) (M (n + d))); [ reflexivity | apply M_div; lia ].
Qed.

Definition compWdig (p : nat) (X : Zhat) (k : nat) : nat :=
  digitsW X (p ^ k) mod (p ^ k).

Lemma compW_coh : forall p (Hp : 2 <= p) X, redcoh p (compWdig p X).
Proof.
  intros p Hp X k. unfold compWdig.
  (* b k = digitsW X (p^k) mod p^k ; b (S k) = digitsW X (p^(S k)) mod p^(S k) *)
  (* Step 1: digitsW X (p^k) = digitsW X (p^(S k)) mod M(p^k)  (raise level)   *)
  assert (Hle : p ^ k <= p ^ (S k)) by (apply Nat.pow_le_mono_r; lia).
  assert (Hraise : digitsW X (p ^ k) = digitsW X (p ^ (S k)) mod (M (p ^ k))).
  { replace (p ^ (S k)) with (p ^ k + (p ^ (S k) - p ^ k)) by lia.
    rewrite (projW_gap (p ^ (S k) - p ^ k) X (p ^ k)); reflexivity. }
  rewrite Hraise.
  (* (y mod M(p^k)) mod p^k = y mod p^k  since p^k | M(p^k) *)
  rewrite (mod_mod_div (p ^ k) (M (p ^ k))) by (apply ppow_div_M; exact Hp).
  (* now: y mod p^k = (y mod p^(S k)) mod p^k ; nested_mod, p^k | p^(S k) *)
  rewrite (PadicIntegers.nested_mod p (digitsW X (p ^ (S k))) k). reflexivity.
Qed.

Definition compW (p : nat) (Hp : 2 <= p) (X : Zhat) : Zp p :=
  exist (redcoh p) (compWdig p X) (compW_coh p Hp X).

Lemma compW_proj : forall p Hp X k,
  projZ p k (compW p Hp X) = digitsW X (p ^ k) mod (p ^ k).
Proof. reflexivity. Qed.

(* the canonical infinite primorial Wzero maps to 0 in every Z_p *)
Lemma compW_Wzero : forall p (Hp : 2 <= p) k,
  projZ p k (compW p Hp Wzero) = projZ p k (Zzero p).
Proof.
  intros p Hp k. rewrite compW_proj.
  change (digitsW Wzero (p ^ k)) with 0. rewrite Nat.Div0.mod_0_l. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — the order<->ring bridge, axiom-free             *)
(* ----------------------------------------------------------------- *)

Theorem profinite_bridge :
  (* Phi is a well-typed cone InvLim -> Zp p reading exponents mod p^n *)
  (forall p Hp X n, projZ p n (Phi p Hp X) = p ^ (val (projL n X)) mod p ^ n)
  (* the order-top infty is p^oo = 0 in every Z_p *)
  /\ (forall p (Hp : 2 <= p) n, projZ p n (Phi p Hp infty) = projZ p n (Zzero p))
  (* naturals map to the (capped) p-adic powers *)
  /\ (forall p (Hp : 2 <= p) m n, projZ p n (Phi p Hp (emb m)) = p ^ (Nat.min m n) mod p ^ n)
  (* compW projects Zhat onto each component Z_p *)
  /\ (forall p Hp X k, projZ p k (compW p Hp X) = digitsW X (p ^ k) mod (p ^ k))
  (* the canonical infinite primorial Wzero is 0 in every Z_p *)
  /\ (forall p (Hp : 2 <= p) k, projZ p k (compW p Hp Wzero) = projZ p k (Zzero p)).
Proof.
  split; [ exact Phi_proj | ].
  split; [ exact Phi_infty | ].
  split; [ exact Phi_emb | ].
  split; [ exact compW_proj | exact compW_Wzero ].
Qed.

Print Assumptions profinite_bridge.

(* ================================================================= *)
(*  END ProfiniteBridge.v                                            *)
(* ================================================================= *)
