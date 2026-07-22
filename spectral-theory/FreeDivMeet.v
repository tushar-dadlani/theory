(* ================================================================= *)
(*  FreeDivMeet.v                                                     *)
(*                                                                    *)
(*  A FREE UNBOUNDED LATTICE and the DIVISIBILITY LATTICE, and their  *)
(*  fixed point defined as the MEET (coincidence) between the two --  *)
(*  a coincidence GUARANTEED, for any two prime powers, by CRT.       *)
(*                                                                    *)
(*  The free unbounded lattice F = nat * nat:  two INDEPENDENT         *)
(*  unbounded chains (exponent axes for two places), meet = pointwise  *)
(*  min, join = pointwise max, monoid sum = pointwise +.  Free and     *)
(*  unbounded: no relation between the two coordinates, no top          *)
(*  element.                                                          *)
(*                                                                    *)
(*  The divisibility lattice: (Z, |), meet = gcd, join = lcm.          *)
(*                                                                    *)
(*  The coding  code (a,b) = p^a * q^b  (p, q distinct primes)         *)
(*  embeds the free lattice into the divisibility lattice.  The        *)
(*  FIXED POINT / meet of the two structures is where the free-lattice *)
(*  operations coincide with the divisibility operations.  On the two  *)
(*  prime-power AXIS generators p^a and q^b this coincidence is EXACT: *)
(*                                                                    *)
(*     gcd (p^a) (q^b) = 1       = code (fmeet (a,0) (0,b))            *)
(*     lcm (p^a) (q^b) = p^a q^b = code (fjoin (a,0) (0,b))            *)
(*                                                                    *)
(*  and CRT -- i.e. the coprimality of the two prime powers -- is      *)
(*  exactly what GUARANTEES it (gcd = 1 = the free lattice's bottom,   *)
(*  lcm = product = the free lattice's join).  Axiom-free over Z.      *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia.
Open Scope Z_scope.

(* ================================================================= *)
(*  1.  THE FREE UNBOUNDED LATTICE  F = nat * nat                     *)
(* ================================================================= *)

Definition F := (nat * nat)%type.

Definition fle  (u v : F) : Prop := (fst u <= fst v)%nat /\ (snd u <= snd v)%nat.
Definition fmeet (u v : F) : F := (Nat.min (fst u) (fst v), Nat.min (snd u) (snd v)).
Definition fjoin (u v : F) : F := (Nat.max (fst u) (fst v), Nat.max (snd u) (snd v)).
Definition fadd  (u v : F) : F := ((fst u + fst v)%nat, (snd u + snd v)%nat).
Definition fbot : F := (0%nat, 0%nat).

(* meet is the greatest lower bound *)
Lemma fmeet_lb_l : forall u v, fle (fmeet u v) u.
Proof. intros [u1 u2] [v1 v2]; unfold fle, fmeet; cbn [fst snd]; lia. Qed.

Lemma fmeet_lb_r : forall u v, fle (fmeet u v) v.
Proof. intros [u1 u2] [v1 v2]; unfold fle, fmeet; cbn [fst snd]; lia. Qed.

Lemma fmeet_glb : forall u v w, fle w u -> fle w v -> fle w (fmeet u v).
Proof. intros [u1 u2] [v1 v2] [w1 w2]; unfold fle, fmeet; cbn [fst snd]; lia. Qed.

(* join is the least upper bound *)
Lemma fjoin_ub_l : forall u v, fle u (fjoin u v).
Proof. intros [u1 u2] [v1 v2]; unfold fle, fjoin; cbn [fst snd]; lia. Qed.

Lemma fjoin_ub_r : forall u v, fle v (fjoin u v).
Proof. intros [u1 u2] [v1 v2]; unfold fle, fjoin; cbn [fst snd]; lia. Qed.

Lemma fjoin_lub : forall u v w, fle u w -> fle v w -> fle (fjoin u v) w.
Proof. intros [u1 u2] [v1 v2] [w1 w2]; unfold fle, fjoin; cbn [fst snd]; lia. Qed.

(* an absorption law -- confirms it is a genuine lattice *)
Lemma fabsorb : forall u v, fmeet u (fjoin u v) = u.
Proof. intros [u1 u2] [v1 v2]; unfold fmeet, fjoin; cbn [fst snd]; f_equal; lia. Qed.

(* fbot is a bottom *)
Lemma fbot_le : forall u, fle fbot u.
Proof. intros [u1 u2]; unfold fle, fbot; cbn [fst snd]; lia. Qed.

(* UNBOUNDED above: no top element *)
Lemma unbounded_above : forall u, exists v, fle u v /\ v <> u.
Proof.
  intros [u1 u2]. exists (S u1, u2). split.
  - unfold fle; cbn [fst snd]; lia.
  - intro Heq; inversion Heq; lia.
Qed.

(* ================================================================= *)
(*  2.  COPRIMALITY OF PRIME POWERS  (the CRT engine)                 *)
(*      rel_prime x y  =>  rel_prime (x^i) (y^j)                       *)
(* ================================================================= *)

Lemma rp_r : forall x y j, rel_prime x y -> rel_prime x (y ^ Z.of_nat j).
Proof.
  intros x y j H; induction j as [|j IH].
  - cbn [Z.of_nat]; rewrite Z.pow_0_r; apply rel_prime_sym; apply rel_prime_1.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
    apply rel_prime_mult; [ exact H | exact IH ].
Qed.

Lemma rp_l : forall x y i, rel_prime x y -> rel_prime (x ^ Z.of_nat i) y.
Proof.
  intros x y i H; apply rel_prime_sym; apply rp_r; apply rel_prime_sym; exact H.
Qed.

Lemma rp_pow_gen : forall x y i j,
  rel_prime x y -> rel_prime (x ^ Z.of_nat i) (y ^ Z.of_nat j).
Proof. intros x y i j H; apply rp_r; apply rp_l; exact H. Qed.

(* ================================================================= *)
(*  3.  THE CODING AND THE CRT COINCIDENCE                            *)
(* ================================================================= *)

Section CRT.

Variables p q : Z.
Hypothesis Hp  : prime p.
Hypothesis Hq  : prime q.
Hypothesis Hpq : p <> q.

(* two distinct primes are coprime *)
Lemma pq_coprime : rel_prime p q.
Proof.
  apply prime_rel_prime; [ exact Hp | ]. intro Hdiv.
  assert (Hd := prime_divisors q Hq p Hdiv).
  destruct Hp as [Hp1 _]; destruct Hq as [Hq1 _].
  destruct Hd as [H | [H | [H | H]]]; lia.
Qed.

(* the embedding of the free lattice into the divisibility lattice *)
Definition code (u : F) : Z := p ^ Z.of_nat (fst u) * q ^ Z.of_nat (snd u).

(* every coded number is positive *)
Lemma code_pos : forall u, 0 < code u.
Proof.
  intros [u1 u2]; unfold code; cbn [fst snd].
  destruct Hp as [Hp1 _]; destruct Hq as [Hq1 _].
  apply Z.mul_pos_pos; apply Z.pow_pos_nonneg; solve [ lia | apply Nat2Z.is_nonneg ].
Qed.

(* code is a monoid homomorphism  (F,+,0) -> (Z,*,1)  *)
Lemma code_00 : code (0%nat, 0%nat) = 1.
Proof. unfold code; cbn [fst snd Z.of_nat]; rewrite !Z.pow_0_r; ring. Qed.

Lemma code_add : forall u v, code (fadd u v) = code u * code v.
Proof.
  intros [u1 u2] [v1 v2]; unfold code, fadd; cbn [fst snd].
  rewrite !Nat2Z.inj_add, !Z.pow_add_r by apply Nat2Z.is_nonneg. ring.
Qed.

Section Axes.

Variables a b : nat.

(* THE CRT MEET: two coprime prime powers meet at 1 (the free bottom) *)
Lemma crt_meet : Z.gcd (code (a, 0%nat)) (code (0%nat, b)) = 1.
Proof.
  unfold code; cbn [fst snd Z.of_nat].
  rewrite !Z.pow_0_r, Z.mul_1_r, Z.mul_1_l.
  apply (proj2 (Zgcd_1_rel_prime _ _)).
  apply rp_pow_gen; exact pq_coprime.
Qed.

(* THE CRT JOIN: their lcm is the full product (the free join) *)
Lemma crt_join :
  Z.lcm (code (a, 0%nat)) (code (0%nat, b)) = code (a, 0%nat) * code (0%nat, b).
Proof.
  assert (H1 : code (a, 0%nat) <> 0) by (pose proof (code_pos (a, 0%nat)); lia).
  assert (H2 : code (0%nat, b) <> 0) by (pose proof (code_pos (0%nat, b)); lia).
  rewrite (proj1 (Z.gcd_1_lcm_mul _ _ H1 H2) crt_meet).
  apply Z.abs_eq.
  pose proof (code_pos (a, 0%nat)); pose proof (code_pos (0%nat, b)); nia.
Qed.

(* the free-lattice meet / join of the two axis generators *)
Lemma fmeet_axes : fmeet (a, 0%nat) (0%nat, b) = (0%nat, 0%nat).
Proof. unfold fmeet; cbn [fst snd]; f_equal; lia. Qed.

Lemma fjoin_axes : fjoin (a, 0%nat) (0%nat, b) = (a, b).
Proof. unfold fjoin; cbn [fst snd]; f_equal; lia. Qed.

Lemma fadd_axes : fadd (a, 0%nat) (0%nat, b) = (a, b).
Proof. unfold fadd; cbn [fst snd]; f_equal; lia. Qed.

(* ----------------------------------------------------------------- *)
(*  THE FIXED POINT: the divisibility meet/join of the two prime-     *)
(*  power axes EQUALS the image, under code, of the free-lattice      *)
(*  meet/join.  This is where the two lattices coincide -- and CRT     *)
(*  (coprimality) is exactly what makes gcd = 1 = code(fmeet).         *)
(* ----------------------------------------------------------------- *)

Theorem crt_lattice_coincidence :
  Z.gcd (code (a, 0%nat)) (code (0%nat, b)) = code (fmeet (a, 0%nat) (0%nat, b))
  /\ Z.lcm (code (a, 0%nat)) (code (0%nat, b)) = code (fjoin (a, 0%nat) (0%nat, b)).
Proof.
  split.
  - rewrite fmeet_axes, crt_meet, code_00; reflexivity.
  - rewrite fjoin_axes, crt_join, <- code_add, fadd_axes; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM -- axiom-free over Z                              *)
(* ----------------------------------------------------------------- *)

Theorem free_div_meet :
  (* the free unbounded lattice *)
  (forall u v w, fle w u -> fle w v -> fle w (fmeet u v))
  /\ (forall u v w, fle u w -> fle v w -> fle (fjoin u v) w)
  /\ (forall u v, fmeet u (fjoin u v) = u)
  /\ (forall u, exists v, fle u v /\ v <> u)
  (* the CRT fixed point: divisibility meet/join = image of free meet/join *)
  /\ Z.gcd (code (a, 0%nat)) (code (0%nat, b)) = code (fmeet (a, 0%nat) (0%nat, b))
  /\ Z.lcm (code (a, 0%nat)) (code (0%nat, b)) = code (fjoin (a, 0%nat) (0%nat, b)).
Proof.
  split; [ exact fmeet_glb | ].
  split; [ exact fjoin_lub | ].
  split; [ exact fabsorb | ].
  split; [ exact unbounded_above | ].
  exact crt_lattice_coincidence.
Qed.

End Axes.
End CRT.

Print Assumptions free_div_meet.

(* ================================================================= *)
(*  END FreeDivMeet.v                                                 *)
(*  Free unbounded lattice (nat*nat) meets the divisibility lattice   *)
(*  (Z, gcd, lcm) at the image of any two prime-power axes; the        *)
(*  coincidence (gcd = 1, lcm = product) is guaranteed by CRT          *)
(*  (coprimality).  ZERO Admitted; Closed under the global context.   *)
(* ================================================================= *)
