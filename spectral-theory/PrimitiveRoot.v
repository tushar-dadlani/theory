(* ================================================================= *)
(*  PrimitiveRoot.v                                                  *)
(*                                                                    *)
(*  PHASE 4b of the Dirichlet-mod-p build: (Z/pZ)^* IS CYCLIC.        *)
(*                                                                    *)
(*     units_cyclic : prime p -> exists g, 1<=g<=p-1 /\ ord p g = p-1. *)
(*                                                                    *)
(*  The order-counting argument.  psi(d) = #{ units of order d }.     *)
(*    psi_le_phi : psi(d) <= phi(d)  -- if a0 has order d, every unit  *)
(*      of order d is a0^i with gcd(i,d)=1 (surjectivity onto the      *)
(*      d-th roots via PolyRootsFp.dth_roots_bound + pow_inj_below);   *)
(*    sum_psi   : sum_{d|p-1} psi(d) = p-1   (partition units by ord); *)
(*    Totient.totient_divisor_sum : sum_{d|p-1} phi(d) = p-1;          *)
(*    squeeze   : psi <= phi termwise with equal sums => psi = phi,    *)
(*      so psi(p-1) = phi(p-1) >= 1 -- a primitive root exists.        *)
(*                                                                    *)
(*  Axiom-free (Closed under the global context).                    *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool.
Require Import ZmodPStar ZmodOrder PolyRootsFp Totient.
Import ListNotations.
Open Scope nat_scope.

Definition psi (p d : nat) : nat :=
  length (filter (fun a => ord p a =? d) (seq 1 (p - 1))).

(* ----------------------------------------------------------------- *)
(*  #{ i in [0,d) : gcd(i,d)=1 }  =  phi(d)                          *)
(* ----------------------------------------------------------------- *)

Lemma coprimes_below_eq_phi : forall d, 1 <= d ->
  length (filter (fun i => Nat.gcd i d =? 1) (seq 0 d)) = phi d.
Proof.
  intros d Hd; unfold phi.
  assert (H0 : seq 0 d = 0 :: seq 1 (d - 1))
    by (replace d with (S (d - 1)) at 1 by lia; reflexivity).
  assert (H1 : seq 1 d = seq 1 (d - 1) ++ [d])
    by (replace d with (S (d - 1)) at 1 by lia; rewrite seq_S; repeat f_equal; lia).
  rewrite H0, H1, filter_app; cbn [filter].
  rewrite Nat.gcd_0_l, Nat.gcd_diag.
  destruct (d =? 1); cbn [length app]; rewrite length_app; cbn [length]; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  A d-th root is a power of a fixed order-d element                *)
(* ----------------------------------------------------------------- *)

Lemma pw_unit : forall p a i, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  1 <= pw p a i <= p - 1.
Proof.
  intros p a i Hp Ha; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hnd : ~ Nat.divide p (a ^ i)) by (apply not_div_pow; [ assumption | apply unit_not_div; exact Ha ]).
  unfold pw; split.
  - assert ((a ^ i) mod p <> 0) by (rewrite Nat.Lcm0.mod_divide; exact Hnd).
    pose proof (Nat.mod_upper_bound (a ^ i) p ltac:(lia)); lia.
  - pose proof (Nat.mod_upper_bound (a ^ i) p ltac:(lia)); lia.
Qed.

Lemma pw_is_root : forall p a i d, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  ord p a = d -> pw p (pw p a i) d = 1.
Proof.
  intros p a i d Hp Ha Hord; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  rewrite <- pw_mul_exp, (Nat.mul_comm i d), pw_mul_exp.
  replace (pw p a d) with 1 by (rewrite <- Hord; symmetry; apply ord_period; assumption).
  apply pw_1; exact Hp2.
Qed.

Lemma root_is_power : forall p a0 d b, prime (Z.of_nat p) -> 1 <= a0 <= p - 1 ->
  ord p a0 = d -> 1 <= b <= p - 1 -> pw p b d = 1 -> exists i, i < d /\ pw p a0 i = b.
Proof.
  intros p a0 d b Hp Ha0 Hord Hb Hbroot.
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  set (roots := filter (fun a => ((a ^ d) mod p =? 1)) (seq 1 (p - 1))).
  set (powers := map (pw p a0) (seq 0 d)).
  assert (Hpow_len : length powers = d)
    by (unfold powers; rewrite length_map, length_seq; reflexivity).
  assert (Hpow_nodup : NoDup powers).
  { unfold powers; apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy; apply in_seq in Hx; apply in_seq in Hy.
    apply (pow_inj_below p a0 x y Hp Ha0); [ rewrite Hord; lia | rewrite Hord; lia | exact Hxy ]. }
  assert (Hsub : incl powers roots).
  { intros z Hz; unfold powers in Hz; apply in_map_iff in Hz as [i [Hzi Hiin]].
    unfold roots; apply filter_In; split.
    - rewrite <- Hzi; pose proof (pw_unit p a0 i Hp Ha0); apply in_seq; lia.
    - rewrite <- Hzi; apply Nat.eqb_eq; apply (pw_is_root p a0 i d Hp Ha0 Hord). }
  assert (Hroots_len : length roots <= d)
    by (unfold roots; apply dth_roots_bound; [ assumption | rewrite <- Hord; apply ord_pos; assumption ]).
  assert (Hle : length roots <= length powers) by (rewrite Hpow_len; exact Hroots_len).
  assert (Hincl2 : incl roots powers)
    by (apply NoDup_length_incl with (l := powers); [ exact Hpow_nodup | exact Hle | exact Hsub ]).
  assert (Hbr : In b roots)
    by (unfold roots; apply filter_In; split; [ apply in_seq; lia | apply Nat.eqb_eq; exact Hbroot ]).
  apply Hincl2 in Hbr; unfold powers in Hbr; apply in_map_iff in Hbr as [i [Hbi Hiin]].
  apply in_seq in Hiin; exists i; split; [ lia | exact Hbi ].
Qed.

(* ----------------------------------------------------------------- *)
(*  An order-d unit is a0^i with gcd(i,d) = 1                        *)
(* ----------------------------------------------------------------- *)

Lemma gcd_of_order : forall p a0 i, prime (Z.of_nat p) -> 1 <= a0 <= p - 1 ->
  i < ord p a0 -> ord p (pw p a0 i) = ord p a0 -> Nat.gcd i (ord p a0) = 1.
Proof.
  intros p a0 i Hp Ha0 Hi Hord.
  set (d := ord p a0).
  assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hd1 : 1 <= d) by (unfold d; apply ord_pos; assumption).
  assert (Hg1 : 1 <= Nat.gcd i d)
    by (destruct (Nat.eq_dec (Nat.gcd i d) 0) as [E|E]; [ apply Nat.gcd_eq_0 in E; lia | lia ]).
  destruct (Nat.gcd_divide_l i d) as [ig Hig].
  destruct (Nat.gcd_divide_r i d) as [dg Hdg].
  assert (Hdg1 : 1 <= dg) by nia.
  assert (Hbe : pw p (pw p a0 i) dg = 1).
  { rewrite <- pw_mul_exp.
    replace (i * dg) with (d * ig) by nia.
    rewrite pw_mul_exp.
    replace (pw p a0 d) with 1 by (unfold d; symmetry; apply ord_period; assumption).
    apply pw_1; exact Hp2. }
  assert (Hpu : 1 <= pw p a0 i <= p - 1) by (apply pw_unit; assumption).
  assert (Hdvd : Nat.divide d dg).
  { unfold d; rewrite <- Hord; apply ord_divides; [ assumption | exact Hpu | exact Hbe ]. }
  destruct Hdvd as [m Hm].
  assert (Hm1 : 1 <= m) by nia.
  assert (dg <= d) by nia.
  assert (d <= dg) by nia.
  assert (Hdgd : dg = d) by lia.
  assert (Hgcd : Nat.gcd i d = 1) by nia.
  exact Hgcd.
Qed.

(* ----------------------------------------------------------------- *)
(*  psi(d) <= phi(d)                                                 *)
(* ----------------------------------------------------------------- *)

Lemma psi_le_phi : forall p d, prime (Z.of_nat p) -> psi p d <= phi d.
Proof.
  intros p d Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold psi.
  destruct (filter (fun a => ord p a =? d) (seq 1 (p - 1))) as [|a0 rest] eqn:Hf.
  - simpl; apply Nat.le_0_l.
  - assert (Ha0 : In a0 (filter (fun a => ord p a =? d) (seq 1 (p - 1))))
      by (rewrite Hf; left; reflexivity).
    apply filter_In in Ha0; destruct Ha0 as [Ha0seq Ha0ord].
    apply in_seq in Ha0seq; apply Nat.eqb_eq in Ha0ord.
    assert (Ha0' : 1 <= a0 <= p - 1) by lia.
    rewrite <- Hf.
    rewrite <- (coprimes_below_eq_phi d) by (rewrite <- Ha0ord; apply ord_pos; assumption).
    rewrite <- (length_map (pw p a0) (filter (fun i => Nat.gcd i d =? 1) (seq 0 d))).
    apply NoDup_incl_length; [ apply NoDup_filter, seq_NoDup | ].
    intros b Hb; apply filter_In in Hb; destruct Hb as [Hbseq Hbord].
    apply in_seq in Hbseq; apply Nat.eqb_eq in Hbord.
    assert (Hb' : 1 <= b <= p - 1) by lia.
    assert (Hbroot : pw p b d = 1) by (rewrite <- Hbord; apply ord_period; [ assumption | exact Hb' ]).
    destruct (root_is_power p a0 d b Hp Ha0' Ha0ord Hb' Hbroot) as [i [Hi Hib]].
    apply in_map_iff; exists i; split; [ exact Hib | ].
    apply filter_In; split.
    + apply in_seq; lia.
    + apply Nat.eqb_eq; rewrite <- Ha0ord; apply (gcd_of_order p a0 i Hp Ha0');
        [ rewrite Ha0ord; exact Hi | rewrite Hib, Hbord, Ha0ord; reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  sum_{d | p-1} psi(d) = p-1                                       *)
(* ----------------------------------------------------------------- *)

Lemma ord_in_divisors : forall p a, prime (Z.of_nat p) -> 1 <= a <= p - 1 ->
  In (ord p a) (divisors (p - 1)).
Proof.
  intros p a Hp Ha; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold divisors; apply filter_In; split.
  - apply in_seq; pose proof (ord_pos p a Hp Ha); pose proof (ord_ub p a Hp Ha); lia.
  - apply Nat.eqb_eq, (proj2 (Nat.Lcm0.mod_divide (p - 1) (ord p a))); apply ord_div_pm1; assumption.
Qed.

Lemma sum_psi : forall p, prime (Z.of_nat p) ->
  fold_right Nat.add 0 (map (psi p) (divisors (p - 1))) = p - 1.
Proof.
  intros p Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold psi.
  rewrite (disjoint_filter_sum (fun a => ord p a) (divisors (p - 1)) (seq 1 (p - 1))
             (divisors_nodup (p - 1))).
  rewrite (filter_all (fun a => existsb (fun d => ord p a =? d) (divisors (p - 1))) (seq 1 (p - 1))).
  - rewrite length_seq; reflexivity.
  - intros a Ha; apply in_seq in Ha; apply existsb_exists.
    exists (ord p a); split; [ apply ord_in_divisors; [ assumption | lia ] | apply Nat.eqb_refl ].
Qed.

(* ----------------------------------------------------------------- *)
(*  the squeeze                                                      *)
(* ----------------------------------------------------------------- *)

Lemma sum_ge : forall (f g : nat -> nat) (l : list nat),
  (forall x, In x l -> f x <= g x) ->
  fold_right Nat.add 0 (map f l) <= fold_right Nat.add 0 (map g l).
Proof.
  intros f g l; induction l as [|a l IH]; cbn [map fold_right]; intro H; [ lia | ].
  assert (f a <= g a) by (apply H; left; reflexivity).
  assert (fold_right Nat.add 0 (map f l) <= fold_right Nat.add 0 (map g l))
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  lia.
Qed.

Lemma sum_eq_termwise : forall (f g : nat -> nat) (l : list nat),
  (forall x, In x l -> f x <= g x) ->
  fold_right Nat.add 0 (map f l) = fold_right Nat.add 0 (map g l) ->
  forall x, In x l -> f x = g x.
Proof.
  intros f g l; induction l as [|a l IH]; intros Hle Hsum x Hx; [ inversion Hx | ].
  cbn [map fold_right] in Hsum.
  assert (Hfa : f a <= g a) by (apply Hle; left; reflexivity).
  assert (Hrest : forall y, In y l -> f y <= g y) by (intros y Hy; apply Hle; right; exact Hy).
  pose proof (sum_ge f g l Hrest) as Hsl.
  assert (Hfa_eq : f a = g a) by lia.
  assert (Hsum_l : fold_right Nat.add 0 (map f l) = fold_right Nat.add 0 (map g l)) by lia.
  destruct Hx as [->|Hx]; [ exact Hfa_eq | apply IH; assumption ].
Qed.

Lemma gcd_1_l : forall n, Nat.gcd 1 n = 1.
Proof.
  intro n; destruct (Nat.gcd_divide_l 1 n) as [k Hk];
    symmetry in Hk; apply Nat.eq_mul_1 in Hk; apply Hk.
Qed.

Lemma phi_pos : forall n, 1 <= n -> 1 <= phi n.
Proof.
  intros n Hn; unfold phi.
  destruct (filter (fun k => Nat.gcd k n =? 1) (seq 1 n)) as [|x l] eqn:E; [ | simpl; lia ].
  exfalso; assert (Hin : In 1 (@nil nat))
    by (rewrite <- E; apply filter_In; split; [ apply in_seq; lia | apply Nat.eqb_eq; apply gcd_1_l ]).
  inversion Hin.
Qed.

(* ----------------------------------------------------------------- *)
(*  PRIMITIVE ROOT EXISTENCE                                         *)
(* ----------------------------------------------------------------- *)

Theorem units_cyclic : forall p, prime (Z.of_nat p) ->
  exists g, 1 <= g <= p - 1 /\ ord p g = p - 1.
Proof.
  intros p Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hpsi_phi : forall d, In d (divisors (p - 1)) -> psi p d = phi d).
  { apply sum_eq_termwise.
    - intros d _; apply psi_le_phi; assumption.
    - rewrite sum_psi by assumption; symmetry; apply totient_divisor_sum; lia. }
  assert (Hpm1 : In (p - 1) (divisors (p - 1))).
  { unfold divisors; apply filter_In; split;
      [ apply in_seq; lia | apply Nat.eqb_eq; rewrite Nat.Div0.mod_same; reflexivity ]. }
  assert (Hpsi : 1 <= psi p (p - 1)).
  { rewrite (Hpsi_phi (p - 1) Hpm1); apply phi_pos; lia. }
  unfold psi in Hpsi.
  destruct (filter (fun a => ord p a =? p - 1) (seq 1 (p - 1))) as [|g rest] eqn:Hf;
    [ simpl in Hpsi; lia | ].
  assert (Hg : In g (filter (fun a => ord p a =? p - 1) (seq 1 (p - 1))))
    by (rewrite Hf; left; reflexivity).
  apply filter_In in Hg; destruct Hg as [Hgseq Hgord].
  apply in_seq in Hgseq; apply Nat.eqb_eq in Hgord.
  exists g; split; [ lia | exact Hgord ].
Qed.

Print Assumptions units_cyclic.

(* ================================================================= *)
(*  END PrimitiveRoot.v  (Phase 4b)                                  *)
(*  (Z/pZ)^* is cyclic: a primitive root of order p-1 exists, by the   *)
(*  order-counting squeeze (psi <= phi, equal sums).  Axiom-free.     *)
(*  Feeds the Dirichlet-character construction (Phase 5).             *)
(* ================================================================= *)
