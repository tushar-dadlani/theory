(* ================================================================= *)
(*  Totient.v                                                        *)
(*                                                                    *)
(*  PHASE 2 of the Dirichlet-mod-p build: Euler's totient phi and     *)
(*  the divisor-sum identity                                         *)
(*                                                                    *)
(*     totient_divisor_sum :  sum_{d | n} phi(d) = n     (n >= 1).    *)
(*                                                                    *)
(*  Proof: partition [1, n] by the key  e(k) := n / gcd(k, n)  (a      *)
(*  divisor of n).  The fiber over e has size phi(e) (bijection        *)
(*  k = (n/e) * j with j in [1,e] coprime to e), and the fibers        *)
(*  partition [1, n], so  sum_{e | n} phi(e) = n.                     *)
(*                                                                    *)
(*  Axiom-free: constructive nat + gcd (no classical logic).          *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia List Permutation Bool.
Import ListNotations.

Definition phi (n : nat) : nat :=
  length (filter (fun k => Nat.gcd k n =? 1) (seq 1 n)).

Definition divisors (n : nat) : list nat :=
  filter (fun d => n mod d =? 0) (seq 1 n).

Lemma divisors_nodup : forall n, NoDup (divisors n).
Proof. intro n; apply NoDup_filter, seq_NoDup. Qed.

(* ----------------------------------------------------------------- *)
(*  Generic list helpers                                             *)
(* ----------------------------------------------------------------- *)

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hinj Hnd; simpl; [ constructor | ].
  rewrite NoDup_cons_iff in Hnd; destruct Hnd as [Hna Hnd].
  rewrite NoDup_cons_iff; split.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Hfy Hy]].
    assert (a = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y; contradiction.
  - apply IH; [ intros x y Hx Hy; apply Hinj; right; assumption | exact Hnd ].
Qed.

Lemma filter_false : forall (L : list nat), filter (fun _ => false) L = [].
Proof. induction L as [|a L IH]; simpl; [ reflexivity | exact IH ]. Qed.

Lemma filter_all : forall (P : nat -> bool) (L : list nat),
  (forall x, In x L -> P x = true) -> filter P L = L.
Proof.
  intros P L; induction L as [|a L IH]; intro H; simpl; [ reflexivity | ].
  rewrite (H a (or_introl eq_refl)); rewrite IH;
    [ reflexivity | intros x Hx; apply H; right; exact Hx ].
Qed.

Lemma filter_or_length : forall (g h : nat -> bool) (l : list nat),
  (forall x, g x && h x = false) ->
  length (filter (fun x => g x || h x) l)
  = length (filter g l) + length (filter h l).
Proof.
  intros g h l Hd; induction l as [|a l IH]; simpl; [ reflexivity | ].
  destruct (g a) eqn:Ga; destruct (h a) eqn:Ha; simpl;
    [ specialize (Hd a); rewrite Ga, Ha in Hd; discriminate
    | rewrite IH; lia | rewrite IH; lia | rewrite IH; lia ].
Qed.

(* sum of disjoint-key fiber counts = count of the union of keys *)
Lemma disjoint_filter_sum : forall (f : nat -> nat) (ks : list nat) (L : list nat),
  NoDup ks ->
  fold_right Nat.add 0 (map (fun d => length (filter (fun k => f k =? d) L)) ks)
  = length (filter (fun k => existsb (fun d => f k =? d) ks) L).
Proof.
  intros f ks L; induction ks as [|d ks IH]; intro Hnd; cbn [map fold_right].
  - cbn [existsb]; rewrite filter_false; reflexivity.
  - rewrite NoDup_cons_iff in Hnd; destruct Hnd as [Hnin Hnd].
    cbn [existsb]; rewrite (IH Hnd).
    symmetry; apply filter_or_length.
    intro k; destruct (f k =? d) eqn:E; simpl; [ | reflexivity ].
    apply Nat.eqb_eq in E.
    apply not_true_iff_false; rewrite existsb_exists; intros [d' [Hin Heq]].
    apply Nat.eqb_eq in Heq; apply Hnin; replace d with d' by lia; exact Hin.
Qed.

(* ----------------------------------------------------------------- *)
(*  The key  n/gcd(k,n)  is a divisor of n                           *)
(* ----------------------------------------------------------------- *)

Lemma key_in_divisors : forall n k, 1 <= k <= n -> In (n / Nat.gcd k n) (divisors n).
Proof.
  intros n k Hk.
  assert (Hg : Nat.gcd k n <> 0) by (intro H; apply Nat.gcd_eq_0 in H; lia).
  destruct (Nat.gcd_divide_r k n) as [q Hq].
  assert (Hqe : n / Nat.gcd k n = q) by (rewrite Hq at 1; apply Nat.div_mul; exact Hg).
  assert (Hgge : 1 <= Nat.gcd k n) by lia.
  unfold divisors; apply filter_In; split.
  - rewrite in_seq, Hqe; nia.
  - rewrite Hqe; apply Nat.eqb_eq, (proj2 (Nat.Lcm0.mod_divide n q));
      exists (Nat.gcd k n); rewrite Hq at 1; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Fiber size:  #{ k in [1,n] : n/gcd(k,n) = e }  =  phi(e)          *)
(* ----------------------------------------------------------------- *)

Lemma count_key_eq_phi : forall n e, In e (divisors n) ->
  length (filter (fun k => (n / Nat.gcd k n) =? e) (seq 1 n)) = phi e.
Proof.
  intros n e He.
  unfold divisors in He; apply filter_In in He; destruct He as [Hein Hmod].
  apply in_seq in Hein; apply Nat.eqb_eq, Nat.Lcm0.mod_divide in Hmod.
  destruct Hmod as [c Hc].                (* n = c * e *)
  assert (He1 : 1 <= e) by lia.
  assert (Hc1 : 1 <= c) by nia.
  assert (Hce : n = c * e) by exact Hc.
  unfold phi.
  transitivity (length (map (Nat.mul c) (filter (fun j => Nat.gcd j e =? 1) (seq 1 e)))).
  - apply Permutation_length, NoDup_Permutation.
    + apply NoDup_filter, seq_NoDup.
    + apply NoDup_map_inj; [ intros x y _ _ Hxy; nia | apply NoDup_filter, seq_NoDup ].
    + intro k; split.
      * intro Hk; apply filter_In in Hk; destruct Hk as [Hkin Hkey].
        apply in_seq in Hkin; apply Nat.eqb_eq in Hkey.
        assert (Hg : Nat.gcd k n <> 0) by (intro H; apply Nat.gcd_eq_0 in H; lia).
        destruct (Nat.gcd_divide_r k n) as [q Hq].          (* n = q * gcd *)
        assert (Hqk : n / Nat.gcd k n = q) by (rewrite Hq at 1; apply Nat.div_mul; exact Hg).
        rewrite Hqk in Hkey; subst q.                        (* n = e * gcd *)
        assert (Hgc : Nat.gcd k n = c) by nia.               (* e*gcd = c*e -> gcd = c *)
        destruct (Nat.gcd_divide_l k n) as [j Hj].           (* k = j * gcd = j * c *)
        rewrite Hgc in Hj.                                   (* k = j * c *)
        apply in_map_iff; exists j; split; [ lia | ].
        apply filter_In; split.
        -- apply in_seq; nia.
        -- apply Nat.eqb_eq.
           assert (Hgcd : Nat.gcd k n = c * Nat.gcd j e).
           { replace k with (c * j) by nia; replace n with (c * e) by nia;
               apply Nat.gcd_mul_mono_l. }
           rewrite Hgc in Hgcd; nia.
      * intro Hk; apply in_map_iff in Hk; destruct Hk as [j [Hkj Hjin]].
        apply filter_In in Hjin; destruct Hjin as [Hjin Hjc].
        apply in_seq in Hjin; apply Nat.eqb_eq in Hjc.
        apply filter_In; split.
        -- apply in_seq; nia.
        -- apply Nat.eqb_eq.
           assert (Hgcd : Nat.gcd k n = c).
           { replace k with (c * j) by nia; replace n with (c * e) by nia;
               rewrite Nat.gcd_mul_mono_l, Hjc; lia. }
           rewrite Hgcd, Hce, (Nat.mul_comm c e), Nat.div_mul by lia; reflexivity.
  - rewrite length_map; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE DIVISOR-SUM IDENTITY                                         *)
(* ----------------------------------------------------------------- *)

Theorem totient_divisor_sum : forall n, 1 <= n ->
  fold_right Nat.add 0 (map phi (divisors n)) = n.
Proof.
  intros n Hn.
  rewrite (map_ext_in phi
             (fun e => length (filter (fun k => (n / Nat.gcd k n) =? e) (seq 1 n)))
             (divisors n))
    by (intros e He; symmetry; apply count_key_eq_phi; exact He).
  rewrite (disjoint_filter_sum (fun k => n / Nat.gcd k n) (divisors n) (seq 1 n)
             (divisors_nodup n)).
  rewrite (filter_all (fun k => existsb (fun d => (n / Nat.gcd k n) =? d) (divisors n))
             (seq 1 n)).
  - rewrite length_seq; reflexivity.
  - intros k Hk; apply in_seq in Hk; apply existsb_exists.
    exists (n / Nat.gcd k n); split; [ apply key_in_divisors; lia | apply Nat.eqb_refl ].
Qed.

Print Assumptions totient_divisor_sum.

(* ================================================================= *)
(*  END Totient.v  (Phase 2)                                         *)
(*  Euler's phi and sum_{d|n} phi(d) = n, by partitioning [1,n] into   *)
(*  gcd-fibers of size phi.  Axiom-free.  Feeds the order-counting     *)
(*  primitive-root proof (Phase 4).                                  *)
(* ================================================================= *)
