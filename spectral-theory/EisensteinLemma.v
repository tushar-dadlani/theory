(* ================================================================= *)
(*  EisensteinLemma.v                                                *)
(*                                                                    *)
(*  EISENSTEIN'S REFINEMENT of Gauss's lemma:  for an odd prime p     *)
(*  and an ODD unit a,                                               *)
(*                                                                    *)
(*      (a/p) = (-1)^( sum_{k=1}^{(p-1)/2} floor(k*a/p) ).            *)
(*                                                                    *)
(*  Proof: from the division identity k*a = p*floor(k*a/p) + (k*a     *)
(*  mod p), summed over k, and the fact that the least-abs residues   *)
(*  permute 1..(p-1)/2, one gets                                     *)
(*      (a-1)*(sum k) = p*(sum floor + mu) - 2*(...),                *)
(*  so (with a, p odd)  mu = sum floor(k*a/p)  (mod 2), and Gauss's   *)
(*  lemma (a/p) = (-1)^mu becomes (-1)^(sum floor).  AXIOM-FREE.     *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Require Import ZmodPStar ZmodOrder LegendreSymbol GaussLemma.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  sum over a list of integers                                 *)
(* ================================================================= *)

Definition Zsum (l : list Z) : Z := fold_right Z.add 0 l.
Lemma Zsum_cons : forall x l, Zsum (x :: l) = x + Zsum l.  Proof. reflexivity. Qed.

Lemma Zsum_perm : forall l l', Permutation l l' -> Zsum l = Zsum l'.
Proof. intros l l' H; induction H; rewrite ?Zsum_cons in *; lia. Qed.

Lemma Zsum_map_add : forall (A:Type)(f g:A->Z) l,
  Zsum (map (fun x => f x + g x) l) = Zsum (map f l) + Zsum (map g l).
Proof.
  intros A f g l; induction l as [|a l IH]; [ reflexivity | ].
  simpl map; rewrite !Zsum_cons, IH; ring.
Qed.

Lemma Zsum_scale : forall (A:Type)(c:Z)(f:A->Z) l,
  Zsum (map (fun x => c * f x) l) = c * Zsum (map f l).
Proof.
  intros A c f l; induction l as [|a l IH]; [ simpl; ring | ].
  simpl map; rewrite !Zsum_cons, IH; ring.
Qed.

Lemma Zsum_const_filter : forall (A:Type)(b:A->bool)(c:Z) l,
  Zsum (map (fun x => if b x then c else 0) l) = c * Z.of_nat (length (filter b l)).
Proof.
  intros A b c l; induction l as [|a l IH]; [ simpl; ring | ].
  simpl map; rewrite Zsum_cons, IH; simpl filter.
  destruct (b a); simpl length; [ rewrite Nat2Z.inj_succ | ]; ring.
Qed.

Lemma Zsum_of_nat : forall l,
  Zsum (map Z.of_nat l) = Z.of_nat (fold_right Nat.add 0%nat l).
Proof.
  induction l as [|a l IH]; [ reflexivity | ].
  simpl map; rewrite Zsum_cons, IH; simpl fold_right; rewrite Nat2Z.inj_add; reflexivity.
Qed.

(* the parity sign depends only on the parity *)
Lemma neg1_pow_even : forall m, (-1) ^ Z.of_nat m = if Nat.even m then 1 else -1.
Proof.
  induction m as [|m IH]; [ reflexivity | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  rewrite IH, Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even m); simpl; ring.
Qed.

Lemma neg1_pow_same : forall m n, Nat.even m = Nat.even n ->
  (-1) ^ Z.of_nat m = (-1) ^ Z.of_nat n.
Proof. intros m n H; rewrite !neg1_pow_even, H; reflexivity. Qed.

(* ================================================================= *)
(*  §2  Eisenstein's refinement                                     *)
(* ================================================================= *)

Section EisSec.
Open Scope nat_scope.

Variable p a : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hodd : p mod 2 = 1.
Hypothesis Hna : ~ Nat.divide p a.
Hypothesis Haodd : a mod 2 = 1.

Notation L := (seq 1 (hlf p)).
Definition floork (k : nat) : nat := (k * a) / p.
Definition Tsum : nat := fold_right Nat.add 0 (map floork L).

Notation SK := (Zsum (map Z.of_nat L)).
Notation SFL := (Zsum (map (fun k => Z.of_nat (floork k)) L)).
Notation SR := (Zsum (map (fun k => Z.of_nat (res p a k)) L)).
Notation SF := (Zsum (map (fun k => Z.of_nat (fres p a k)) L)).
Notation Mz := (Z.of_nat (mu p a)).

Lemma EHp3 : 3 <= p.
Proof. destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hodd | pose proof (prime_ge_2 _ Hp); lia ]. Qed.

(* (a-1)*SK = p*SFL + SR *)
Lemma eis_div : (Z.of_nat a * SK = Z.of_nat p * SFL + SR)%Z.
Proof.
  transitivity (Zsum (map (fun k => Z.of_nat (k * a)) L)).
  - rewrite <- Zsum_scale; f_equal; apply map_ext; intro k.
    rewrite Nat2Z.inj_mul; ring.
  - rewrite (map_ext (fun k => Z.of_nat (k * a))
              (fun k => Z.of_nat p * Z.of_nat (floork k) + Z.of_nat (res p a k))%Z).
    + rewrite Zsum_map_add, Zsum_scale; reflexivity.
    + intro k; unfold floork, res.
      rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add; f_equal.
      rewrite Nat.mul_comm; apply Nat.div_mod_eq.
Qed.

(* SF = SK  (permutation) *)
Lemma eis_perm : (SF = SK)%Z.
Proof.
  rewrite <- (map_map (fres p a) Z.of_nat).
  apply Zsum_perm, Permutation_map, fres_perm; assumption.
Qed.

(* SR + 2*U = SF + p*mu   (no subtraction) *)
Lemma eis_res :
  (SR + 2 * Zsum (map (fun k => if negb (res p a k <=? hlf p)%nat
                               then Z.of_nat (fres p a k) else 0) L)
   = SF + Z.of_nat p * Mz)%Z.
Proof.
  rewrite <- Zsum_scale, <- Zsum_map_add.
  unfold mu; rewrite <- (Zsum_const_filter nat (fun k => negb (res p a k <=? hlf p)) (Z.of_nat p) L).
  rewrite <- Zsum_map_add.
  f_equal; apply map_ext_in; intros k Hk; apply in_seq in Hk.
  pose proof (res_bound p a Hp Hodd Hna k ltac:(lia)) as Hb; unfold fres.
  destruct (res p a k <=? hlf p) eqn:E; cbn [negb].
  - apply Nat.leb_le in E; ring.
  - apply Nat.leb_gt in E; rewrite Nat2Z.inj_sub by lia; ring.
Qed.

(* mu and the floor-sum have the same parity *)
Lemma eis_parity : Nat.even (mu p a) = Nat.even Tsum.
Proof.
  pose proof EHp3 as Hp3.
  set (U := Zsum (map (fun k => if negb (res p a k <=? hlf p)
                                then Z.of_nat (fres p a k) else 0%Z) L)).
  (* linear identity:  (a-1)*SK + 2*U = p*(SFL + Mz) *)
  assert (Hlin : ((Z.of_nat a - 1) * SK + 2 * U = Z.of_nat p * (SFL + Mz))%Z).
  { pose proof eis_div as H1; pose proof eis_perm as H2; pose proof eis_res as H3.
    fold U in H3; rewrite <- H2 in H1; nia. }
  (* a, p odd *)
  assert (Ha2 : exists a', (Z.of_nat a - 1 = 2 * a')%Z).
  { pose proof (Nat.div_mod_eq a 2) as Hdm; rewrite Haodd in Hdm.
    exists (Z.of_nat (a / 2)); rewrite Hdm at 1; rewrite Nat2Z.inj_add, Nat2Z.inj_mul; simpl; ring. }
  assert (Hp2 : exists p', (Z.of_nat p = 2 * p' + 1)%Z).
  { pose proof (Nat.div_mod_eq p 2) as Hdm; rewrite Hodd in Hdm.
    exists (Z.of_nat (p / 2)); rewrite Hdm at 1; rewrite Nat2Z.inj_add, Nat2Z.inj_mul; simpl; ring. }
  destruct Ha2 as [a' Ha']; destruct Hp2 as [p' Hp'].
  assert (HSFL : (SFL = Z.of_nat Tsum)%Z).
  { unfold Tsum; rewrite <- Zsum_of_nat, map_map; reflexivity. }
  (* 2 | (SFL + Mz) *)
  assert (Heven : exists w, (SFL + Mz = 2 * w)%Z).
  { exists (a' * SK + U - p' * (SFL + Mz))%Z.
    rewrite Ha', Hp' in Hlin; nia. }
  destruct Heven as [w Hw]; rewrite HSFL in Hw.
  assert (Hnat : Nat.Even (Tsum + mu p a)).
  { exists (Z.to_nat w); apply Nat2Z.inj.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id by nia; lia. }
  assert (He : Nat.even (Tsum + mu p a) = true) by (apply Nat.even_spec; exact Hnat).
  rewrite Nat.even_add in He.
  destruct (Nat.even Tsum), (Nat.even (mu p a)); simpl in He; try discriminate; reflexivity.
Qed.

(* ================================================================= *)
(*  §3  EISENSTEIN'S REFINEMENT                                      *)
(* ================================================================= *)

Theorem legendre_eisenstein : legendre p a = ((-1) ^ Z.of_nat Tsum)%Z.
Proof.
  rewrite (legendre_gauss p a Hp Hodd Hna).
  apply neg1_pow_same, eis_parity.
Qed.

End EisSec.

Print Assumptions legendre_eisenstein.

(* ================================================================= *)
(*  END EisensteinLemma.v                                            *)
(*  Eisenstein's refinement (a/p) = (-1)^(sum_{k=1}^{(p-1)/2}         *)
(*  floor(k*a/p)) for odd prime p and odd unit a, from Gauss's lemma  *)
(*  and the parity mu = sum floor(k*a/p) (mod 2).  Closed under the   *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
