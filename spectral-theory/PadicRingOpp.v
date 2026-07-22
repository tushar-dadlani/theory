(* ================================================================= *)
(*  PadicRingOpp.v                                                    *)
(*                                                                    *)
(*  GAP-FILL: the ADDITIVE INVERSE of Z_p -- upgrading PadicRing's      *)
(*  commutative SEMIRING to a full commutative RING.  Axiom-free.      *)
(*                                                                    *)
(*  The negation is (-a) at level n = (p^n - a n) mod p^n.  The one      *)
(*  subtlety (deferred in PadicRing) is that this is COHERENT across     *)
(*  levels despite nat TRUNCATED subtraction: neg_coh proves            *)
(*    (p^n - a n) mod p^n = (p^(S n) - a (S n)) mod p^n                 *)
(*  by the div/mod decomposition  a(S n) = p^n * k + a n  (k < p),       *)
(*  so  p^(S n) - a(S n) = (p^n - a n) + (p-k-1) p^n  reduces to the     *)
(*  same residue.  Then Zadd_opp_l : (-X) + X = 0, giving the ring.     *)
(* ================================================================= *)

Require Import PadicIntegers PadicRing.
From Stdlib Require Import Arith Lia.

Section ZpOpp.

Variable p : nat.
Hypothesis Hp : 2 <= p.

(* coherence of the negation across levels (nat truncated subtraction) *)
Lemma neg_coh : forall a, redcoh p a -> forall n,
  (p ^ n - a n) mod p ^ n = (p ^ S n - a (S n)) mod p ^ n.
Proof.
  intros a Ha n.
  assert (Hpn : p ^ n <> 0) by (apply Nat.pow_nonzero; lia).
  assert (Hpos : 0 < p ^ n) by lia.
  assert (Hlt : a n < p ^ n)
    by (rewrite (Ha n); apply Nat.mod_upper_bound; exact Hpn).
  assert (HltS : a (S n) < p ^ S n)
    by (rewrite (Ha (S n)); apply Nat.mod_upper_bound; apply Nat.pow_nonzero; lia).
  pose proof (Nat.div_mod_eq (a (S n)) (p ^ n)) as Hdm.
  assert (Hmod : a (S n) mod p ^ n = a n) by (rewrite (Ha n); reflexivity).
  set (k := a (S n) / p ^ n) in *.
  rewrite Hmod in Hdm.                 (* Hdm : a(Sn) = p^n * k + a n *)
  rewrite Nat.pow_succ_r' in HltS.     (* HltS : a(Sn) < p * p^n *)
  assert (Hk : k < p) by nia.
  rewrite Nat.pow_succ_r'.
  replace (p * p ^ n - a (S n)) with ((p ^ n - a n) + (p - k - 1) * p ^ n) by nia.
  rewrite Nat.Div0.mod_add; reflexivity.
Qed.

Definition ropp (a : nat -> nat) : nat -> nat := fun n => (p ^ n - a n) mod p ^ n.

Lemma redcoh_opp : forall a, redcoh p a -> redcoh p (ropp a).
Proof.
  intros a Ha n; unfold ropp.
  rewrite (PadicIntegers.nested_mod p (p ^ S n - a (S n)) n).
  exact (neg_coh a Ha n).
Qed.

Definition Zopp (X : Zp p) : Zp p :=
  exist (redcoh p) (ropp (digits p X)) (redcoh_opp (digits p X) (proj2_sig X)).

(* the additive inverse law: (-X) + X = 0 -- the ring upgrade *)
Theorem Zadd_opp_l : forall X, Zeq p (Zadd p (Zopp X) X) (Zzero p).
Proof.
  intros X n; rewrite (PadicRing.digits_add p).
  change (digits p (Zopp X) n) with ((p ^ n - digits p X n) mod p ^ n).
  rewrite Nat.Div0.add_mod_idemp_l.
  assert (Hlt : digits p X n < p ^ n)
    by (apply (PadicRing.redcoh_lt p Hp); exact (proj2_sig X)).
  replace (p ^ n - digits p X n + digits p X n) with (p ^ n) by lia.
  rewrite Nat.Div0.mod_same, (PadicRing.digits_zero p); reflexivity.
Qed.

End ZpOpp.

Print Assumptions Zadd_opp_l.

(* ================================================================= *)
(*  END PadicRingOpp.v                                                *)
(*  Z_p has additive inverses (Zopp, Zadd_opp_l): combined with         *)
(*  PadicRing.Zp_comm_semiring, Z_p is a COMMUTATIVE RING.  The         *)
(*  negation is coherent across levels despite nat truncated            *)
(*  subtraction.  ZERO Admitted; Closed under the global context.       *)
(* ================================================================= *)
