(* ================================================================= *)
(*  GaussLemma.v                                                     *)
(*                                                                    *)
(*  GAUSS'S LEMMA:  for an odd prime p and a unit a,                  *)
(*                                                                    *)
(*      (a/p) = (-1)^mu,                                             *)
(*                                                                    *)
(*  where mu = #{ k in [1,(p-1)/2] : (k*a) mod p > (p-1)/2 }.        *)
(*                                                                    *)
(*  Proof: the least-absolute residues of a, 2a, ..., ((p-1)/2)a      *)
(*  are, up to sign, a permutation of 1, 2, ..., (p-1)/2.  Taking     *)
(*  the product mod p,                                               *)
(*      a^((p-1)/2) * ((p-1)/2)!  =  (-1)^mu * ((p-1)/2)!  (mod p),   *)
(*  and cancelling ((p-1)/2)! (a unit) gives a^((p-1)/2) = (-1)^mu,   *)
(*  hence (a/p) = (-1)^mu by Euler's criterion.  AXIOM-FREE.         *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Require Import ZmodPStar ZmodOrder LegendreSymbol.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  product over a list of integers                             *)
(* ================================================================= *)

Definition Zprod (l : list Z) : Z := fold_right Z.mul 1 l.
Lemma Zprod_cons : forall x l, Zprod (x :: l) = x * Zprod l.  Proof. reflexivity. Qed.

Lemma Zprod_perm : forall l l', Permutation l l' -> Zprod l = Zprod l'.
Proof. intros l l' H; induction H; rewrite ?Zprod_cons in *; try lia; try congruence. Qed.

Lemma Zprod_map_mul : forall (A:Type)(f g:A->Z) l,
  Zprod (map (fun x => f x * g x) l) = Zprod (map f l) * Zprod (map g l).
Proof.
  intros A f g l; induction l as [|a l IH]; [ reflexivity | ].
  simpl map; rewrite !Zprod_cons, IH; ring.
Qed.

Lemma Zprod_mod_cong : forall (A:Type)(f g:A->Z) l P,
  (forall x, In x l -> f x mod P = g x mod P) ->
  Zprod (map f l) mod P = Zprod (map g l) mod P.
Proof.
  intros A f g l P; induction l as [|a l IH]; intro H; [ reflexivity | ].
  simpl map; rewrite !Zprod_cons, Zmult_mod, (H a (or_introl eq_refl)).
  rewrite (IH (fun x Hx => H x (or_intror Hx))), <- Zmult_mod; reflexivity.
Qed.

Lemma Zprod_const : forall (A:Type)(c:Z)(l:list A),
  Zprod (map (fun _ => c) l) = c ^ Z.of_nat (length l).
Proof.
  intros A c l; induction l as [|a l IH]; [ reflexivity | ].
  simpl map; rewrite Zprod_cons, IH; simpl length.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity.
Qed.

Lemma Zprod_signs : forall (A:Type)(b:A->bool) l,
  Zprod (map (fun x => if b x then (-1) else 1) l)
  = (-1) ^ Z.of_nat (length (filter b l)).
Proof.
  intros A b l; induction l as [|a l IH]; [ reflexivity | ].
  simpl map; rewrite Zprod_cons, IH; simpl filter.
  destruct (b a); simpl length;
    [ rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring | ring ].
Qed.

(* ================================================================= *)
(*  §2  the Gauss-lemma set-up over a fixed odd prime and unit       *)
(* ================================================================= *)

Section GaussSec.
Open Scope nat_scope.

Variable p a : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hodd : p mod 2 = 1.
Hypothesis Hna : ~ Nat.divide p a.

Lemma GHp3 : 3 <= p.
Proof. destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hodd | pose proof (prime_ge_2 _ Hp); lia ]. Qed.
Lemma GHH : 2 * hlf p = p - 1.
Proof. apply two_hlf; [ exact Hodd | pose proof GHp3; lia ]. Qed.
Lemma GHnda : ~ Nat.divide p a.
Proof. exact Hna. Qed.

Definition res (k : nat) : nat := (k * a) mod p.
Definition fres (k : nat) : nat := if res k <=? hlf p then res k else p - res k.
Definition sgn (k : nat) : Z := if res k <=? hlf p then 1%Z else (-1)%Z.
Definition mu : nat := length (filter (fun k => negb (res k <=? hlf p)) (seq 1 (hlf p))).

Lemma res_bound : forall k, 1 <= k <= hlf p -> 1 <= res k <= p - 1.
Proof.
  intros k Hk; pose proof GHp3 as Hp3; pose proof GHH as HH.
  assert (Hub : res k < p) by (unfold res; apply Nat.mod_upper_bound; lia).
  assert (Hnz : res k <> 0).
  { unfold res; intro E.
    assert (Hd : Nat.divide p (k * a)) by (apply Nat.Lcm0.mod_divide; exact E).
    destruct (prime_mult_nat p k a Hp Hd) as [H|H];
      [ apply (unit_not_div p k ltac:(lia)) | apply GHnda ]; exact H. }
  lia.
Qed.

Lemma fres_bound : forall k, 1 <= k <= hlf p -> 1 <= fres k <= hlf p.
Proof.
  intros k Hk; pose proof GHH as HH; pose proof (res_bound k Hk) as Hb.
  unfold fres; destruct (res k <=? hlf p) eqn:E.
  - apply Nat.leb_le in E; lia.
  - apply Nat.leb_gt in E; lia.
Qed.

(* res k = +/- fres k  (mod p) *)
Lemma res_sgn_cong : forall k, 1 <= k <= hlf p ->
  (Z.of_nat (res k) mod Z.of_nat p)%Z = ((sgn k * Z.of_nat (fres k)) mod Z.of_nat p)%Z.
Proof.
  intros k Hk; pose proof (res_bound k Hk) as Hb.
  unfold sgn, fres; destruct (res k <=? hlf p).
  - rewrite Z.mul_1_l; reflexivity.
  - rewrite Nat2Z.inj_sub by lia.
    replace ((-1) * (Z.of_nat p - Z.of_nat (res k)))%Z
      with (Z.of_nat (res k) + (-1) * Z.of_nat p)%Z by ring.
    rewrite Z_mod_plus_full; reflexivity.
Qed.

(* the map k |-> fres k is injective on [1, (p-1)/2] *)
Lemma fres_inj : forall i j, 1 <= i <= hlf p -> 1 <= j <= hlf p -> fres i = fres j -> i = j.
Proof.
  intros i j Hi Hj Hij; pose proof GHp3 as Hp3; pose proof GHH as HH.
  (* equal residues => equal indices *)
  assert (Hcancel : res i = res j -> i = j).
  { intro E.
    assert (Hm : i mod p = j mod p).
    { apply (cancel_mod p a i j Hp GHnda).
      unfold res in E; rewrite (Nat.mul_comm i a), (Nat.mul_comm j a) in E; exact E. }
    rewrite (Nat.mod_small i p) in Hm by lia; rewrite (Nat.mod_small j p) in Hm by lia; exact Hm. }
  (* res i + res j = p is impossible *)
  assert (Hsum : res i + res j = p -> False).
  { intro Hs.
    assert (Hd : Nat.divide p ((i + j) * a)).
    { apply Nat.Lcm0.mod_divide.
      rewrite Nat.mul_add_distr_r, Nat.Div0.add_mod.
      unfold res in Hs; rewrite Hs; apply Nat.Div0.mod_same. }
    destruct (prime_mult_nat p (i + j) a Hp Hd) as [Hd'|Hd'].
    - pose proof (Nat.divide_pos_le p (i + j) ltac:(lia) Hd'); lia.
    - apply GHnda; exact Hd'. }
  (* res k is fres k or p - fres k *)
  assert (Hpr : forall k, 1 <= k <= hlf p -> res k = fres k \/ res k = p - fres k).
  { intros k Hk; pose proof (res_bound k Hk); unfold fres; destruct (res k <=? hlf p) eqn:E;
      [ left; reflexivity | apply Nat.leb_gt in E; right; lia ]. }
  destruct (Hpr i Hi) as [Ei|Ei]; destruct (Hpr j Hj) as [Ej|Ej];
    rewrite Hij in Ei; pose proof (fres_bound j Hj) as Hfb.
  - apply Hcancel; rewrite Ei, Ej; reflexivity.
  - exfalso; apply Hsum; rewrite Ei, Ej; lia.
  - exfalso; apply Hsum; rewrite Ei, Ej; lia.
  - apply Hcancel; rewrite Ei, Ej; reflexivity.
Qed.

(* hence {fres k} is a permutation of [1, (p-1)/2] *)
Lemma fres_perm : Permutation (map fres (seq 1 (hlf p))) (seq 1 (hlf p)).
Proof.
  apply NoDup_Permutation_bis.
  - apply Totient.NoDup_map_inj; [ | apply seq_NoDup ].
    intros i j Hi Hj; apply in_seq in Hi; apply in_seq in Hj; apply fres_inj; lia.
  - rewrite length_map; reflexivity.
  - intros y Hy; apply in_map_iff in Hy; destruct Hy as [k [Hk Hkin]].
    apply in_seq in Hkin; apply in_seq; pose proof (fres_bound k ltac:(lia)); lia.
Qed.

(* ================================================================= *)
(*  §3  the two product computations and Gauss's lemma              *)
(* ================================================================= *)

Notation FACT := (Zprod (map Z.of_nat (seq 1 (hlf p)))).

(* the factorial ((p-1)/2)! is a unit mod p *)
Lemma fact_coprime : ~ (Z.of_nat p | FACT).
Proof.
  pose proof GHp3 as Hp3; pose proof GHH as HH.
  assert (Hall : forall k, In k (seq 1 (hlf p)) -> 1 <= k <= hlf p)
    by (intros k Hk; apply in_seq in Hk; lia).
  revert Hall; generalize (seq 1 (hlf p)); intro l; induction l as [|k l IH]; intro Hall.
  - simpl; intro Hdv; pose proof (Z.divide_pos_le _ 1 ltac:(lia) Hdv); lia.
  - simpl map; rewrite Zprod_cons; intro Hdv.
    destruct (prime_mult (Z.of_nat p) Hp _ _ Hdv) as [H1|H1].
    + assert (Hk : 1 <= k <= hlf p) by (apply Hall; left; reflexivity).
      pose proof (Z.divide_pos_le (Z.of_nat p) (Z.of_nat k) ltac:(lia) H1); lia.
    + apply IH; [ intros x Hx; apply Hall; right; exact Hx | exact H1 ].
Qed.

(* product of residues = (-1)^mu * ((p-1)/2)!  (mod p) *)
Lemma prod_res_sign :
  (Zprod (map (fun k => Z.of_nat (res k)) (seq 1 (hlf p))) mod Z.of_nat p
   = ((-1) ^ Z.of_nat mu * FACT) mod Z.of_nat p)%Z.
Proof.
  rewrite (Zprod_mod_cong nat (fun k => Z.of_nat (res k))
             (fun k => (sgn k * Z.of_nat (fres k))%Z) (seq 1 (hlf p)) (Z.of_nat p)).
  2:{ intros k Hk; apply in_seq in Hk; apply res_sgn_cong; lia. }
  rewrite Zprod_map_mul; f_equal; f_equal.
  - (* Zprod (map sgn ..) = (-1)^mu *)
    rewrite (map_ext sgn (fun k => if negb (res k <=? hlf p) then (-1)%Z else 1%Z))
      by (intro k; unfold sgn; destruct (res k <=? hlf p); reflexivity).
    apply (Zprod_signs nat (fun k => negb (res k <=? hlf p))).
  - (* Zprod (map (Z.of_nat o fres) ..) = FACT  (permutation) *)
    rewrite <- map_map; apply Zprod_perm, Permutation_map, fres_perm.
Qed.

(* product of residues = ((p-1)/2)! * a^((p-1)/2)  (mod p) *)
Lemma prod_res_val :
  (Zprod (map (fun k => Z.of_nat (res k)) (seq 1 (hlf p))) mod Z.of_nat p
   = (FACT * Z.of_nat a ^ Z.of_nat (hlf p)) mod Z.of_nat p)%Z.
Proof.
  rewrite (Zprod_mod_cong nat (fun k => Z.of_nat (res k))
             (fun k => (Z.of_nat k * Z.of_nat a)%Z) (seq 1 (hlf p)) (Z.of_nat p)).
  2:{ intros k _; unfold res.
      rewrite Nat2Z.inj_mod, Zmod_mod, Nat2Z.inj_mul; reflexivity. }
  rewrite Zprod_map_mul, Zprod_const, length_seq; reflexivity.
Qed.

(* the parity sign is +/- 1 *)
Lemma neg1_pow_pm1 : forall n, ((-1) ^ Z.of_nat n = 1)%Z \/ ((-1) ^ Z.of_nat n = -1)%Z.
Proof.
  induction n as [|n IH]; [ left; reflexivity | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct IH as [E|E]; rewrite E; [ right | left ]; ring.
Qed.

(* GAUSS'S LEMMA *)
Theorem legendre_gauss : legendre p a = ((-1) ^ Z.of_nat mu)%Z.
Proof.
  pose proof GHp3 as Hp3.
  (* a^((p-1)/2) = (-1)^mu  (mod p), by cancelling FACT *)
  assert (Hcong : ((FACT * Z.of_nat a ^ Z.of_nat (hlf p)) mod Z.of_nat p
                  = (FACT * (-1) ^ Z.of_nat mu) mod Z.of_nat p)%Z).
  { rewrite <- prod_res_val, prod_res_sign; f_equal; ring. }
  assert (Hdvd : (Z.of_nat p | Z.of_nat a ^ Z.of_nat (hlf p) - (-1) ^ Z.of_nat mu)%Z).
  { assert (Hpf : (Z.of_nat p | FACT * (Z.of_nat a ^ Z.of_nat (hlf p) - (-1) ^ Z.of_nat mu))%Z).
    { apply Z.mod_divide; [ lia | ].
      rewrite Z.mul_sub_distr_l, Zminus_mod, Hcong, <- Zminus_mod, Z.sub_diag; reflexivity. }
    destruct (prime_mult (Z.of_nat p) Hp _ _ Hpf) as [H|H];
      [ exfalso; apply fact_coprime; exact H | exact H ]. }
  (* so a^((p-1)/2) = (-1)^mu (mod p) *)
  assert (Hac : ((Z.of_nat a ^ Z.of_nat (hlf p)) mod Z.of_nat p
                = ((-1) ^ Z.of_nat mu) mod Z.of_nat p)%Z).
  { destruct Hdvd as [c Hc].
    replace (Z.of_nat a ^ Z.of_nat (hlf p))%Z
      with ((-1) ^ Z.of_nat mu + c * Z.of_nat p)%Z by lia.
    rewrite Z_mod_plus_full; reflexivity. }
  (* connect to Euler's criterion and pin the sign *)
  apply (sign_mod_inj p _ _ Hp3).
  - apply legendre_pm1; exact Hna.
  - apply neg1_pow_pm1.
  - rewrite <- Hac.
    rewrite <- (legendre_euler p a Hp Hodd Hna).
    unfold pw; rewrite Nat2Z.inj_mod, Zmod_mod, Nat2Z.inj_pow; reflexivity.
Qed.

End GaussSec.

Print Assumptions legendre_gauss.

(* ================================================================= *)
(*  END GaussLemma.v                                                 *)
(*  Gauss's lemma  (a/p) = (-1)^mu,  mu = #{ k in [1,(p-1)/2] :       *)
(*  (k*a) mod p > (p-1)/2 }, via the least-absolute-residue           *)
(*  permutation and the product a^((p-1)/2)*H! = (-1)^mu*H! (mod p).  *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
