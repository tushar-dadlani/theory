(* ================================================================= *)
(*  VonMangoldtGlobal.v                                              *)
(*                                                                    *)
(*  THE GLOBAL VON MANGOLDT IDENTITY:  sum_{d | n} Lambda(d) = log n.  *)
(*                                                                    *)
(*  This globalises VonMangoldt (which proved Lambda = mu * log per    *)
(*  single prime) to a genuine arithmetic function Lambda : nat -> R    *)
(*  over ALL n, and proves the fundamental identity                    *)
(*     sum over divisors d of n of Lambda(d) = ln n.                   *)
(*  It is the arithmetic crux of the contour-free prime bridge (the     *)
(*  input to Chebyshev's psi(x) ~ x, alongside AbelSummation).         *)
(*                                                                    *)
(*  Everything stays in nat (Nat.gauss for coprimality) + R (for ln);  *)
(*  no complex analysis, no Z.  Uses the classical Reals axioms         *)
(*  (quarantined) for ln.                                             *)
(*                                                                    *)
(*  CHECKPOINT A (this file, part 1): the smallest-prime-factor spf,    *)
(*  nat-primality, the divisor sum dsum, and its Permutation-           *)
(*  invariance.  Lambda, its characterisation, and the identity build   *)
(*  on top.                                                           *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia PeanoNat List Permutation Reals Lra.
Import ListNotations.

(* ================================================================= *)
(*  1.  SMALLEST PRIME FACTOR                                         *)
(* ================================================================= *)

Fixpoint least_div (fuel k n : nat) : nat :=
  match fuel with
  | O => n
  | S f => if Nat.eqb (n mod k) 0 then k else least_div f (S k) n
  end.

Definition spf (n : nat) : nat := least_div n 2 n.

Lemma least_div_divides : forall fuel k n,
  2 <= k -> k <= n -> (n - k < fuel) -> Nat.divide (least_div fuel k n) n.
Proof.
  induction fuel as [|f IH]; intros k n Hk Hkn Hf; [ lia | ].
  simpl. destruct (Nat.eqb (n mod k) 0) eqn:E.
  - apply Nat.eqb_eq, Nat.Lcm0.mod_divide in E; exact E.
  - destruct (Nat.eq_dec k n) as [->|Hne];
      [ rewrite Nat.Div0.mod_same in E; discriminate | apply IH; lia ].
Qed.

Lemma least_div_least : forall fuel k n j,
  2 <= k -> k <= n -> k <= j -> j < least_div fuel k n -> (n - k < fuel) -> ~ Nat.divide j n.
Proof.
  induction fuel as [|f IH]; intros k n j Hk Hkn Hkj Hjld Hf; [ simpl in Hjld; lia | ].
  simpl in Hjld. destruct (Nat.eqb (n mod k) 0) eqn:E; [ lia | ].
  assert (Hklt : k < n)
    by (destruct (Nat.eq_dec k n) as [->|]; [ rewrite Nat.Div0.mod_same in E; discriminate | lia ]).
  destruct (Nat.eq_dec j k) as [->|Hne].
  - intro Hd; apply Nat.Lcm0.mod_divide in Hd; rewrite Hd in E; discriminate.
  - apply (IH (S k) n j); lia.
Qed.

Lemma least_div_ge2 : forall fuel k n, 2 <= k -> 2 <= n -> 2 <= least_div fuel k n.
Proof.
  induction fuel as [|f IH]; intros k n Hk Hn; simpl; [ lia | ].
  destruct (Nat.eqb (n mod k) 0); [ lia | apply IH; lia ].
Qed.

Lemma spf_divides : forall n, 2 <= n -> Nat.divide (spf n) n.
Proof. intros n Hn; unfold spf; apply least_div_divides; lia. Qed.

Lemma spf_ge2 : forall n, 2 <= n -> 2 <= spf n.
Proof. intros n Hn; unfold spf; apply least_div_ge2; lia. Qed.

Lemma spf_least : forall n e, 2 <= n -> 2 <= e -> e < spf n -> ~ Nat.divide e n.
Proof. intros n e Hn He Helt; unfold spf in *; apply (least_div_least n 2 n e); lia. Qed.

(* ================================================================= *)
(*  2.  NAT PRIMALITY, and spf is prime                              *)
(* ================================================================= *)

Definition nprime (p : nat) : Prop :=
  2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.

Lemma spf_nprime : forall n, 2 <= n -> nprime (spf n).
Proof.
  intros n Hn; split; [ apply spf_ge2; exact Hn | ].
  intros d Hd.
  assert (Hp2 : 2 <= spf n) by (apply spf_ge2; exact Hn).
  assert (Hdle : d <= spf n) by (apply Nat.divide_pos_le; [ lia | exact Hd ]).
  assert (Hd1 : 1 <= d) by (destruct d; [ destruct Hd as [x Hx]; lia | lia ]).
  destruct (Nat.eq_dec d 1) as [->|Hne1]; [ left; reflexivity | ].
  destruct (Nat.eq_dec d (spf n)) as [->|Hnep]; [ right; reflexivity | exfalso ].
  (* 2 <= d < spf n and d | spf n | n  -> d | n, contradicting minimality *)
  apply (spf_least n d Hn); [ lia | lia | ].
  apply Nat.divide_trans with (spf n); [ exact Hd | apply spf_divides; exact Hn ].
Qed.

(* ================================================================= *)
(*  3.  DIVISORS AND THE DIVISOR SUM                                 *)
(* ================================================================= *)

Definition divisors (n : nat) : list nat :=
  filter (fun d => Nat.eqb (n mod d) 0) (seq 1 n).

Lemma in_divisors : forall n d,
  In d (divisors n) <-> (1 <= d <= n /\ Nat.divide d n).
Proof.
  intros n d; unfold divisors; rewrite filter_In, in_seq; split.
  - intros [[H1 H2] Hmod]; split; [ lia | ].
    apply Nat.Lcm0.mod_divide; apply Nat.eqb_eq; exact Hmod.
  - intros [[H1 H2] Hdvd]; split; [ lia | ].
    apply Nat.eqb_eq, Nat.Lcm0.mod_divide; exact Hdvd.
Qed.

Lemma divisors_nodup : forall n, NoDup (divisors n).
Proof. intro n; unfold divisors; apply NoDup_filter, seq_NoDup. Qed.

Definition dsum (f : nat -> R) (n : nat) : R := fold_right Rplus 0%R (map f (divisors n)).

(* fold_right Rplus is invariant under permutation *)
Lemma Rsum_perm : forall (l l' : list R), Permutation l l' ->
  fold_right Rplus 0%R l = fold_right Rplus 0%R l'.
Proof.
  intros l l' H; induction H; simpl;
    [ reflexivity | rewrite IHPermutation; reflexivity
    | ring | rewrite IHPermutation1, IHPermutation2; reflexivity ].
Qed.

Lemma dsum_perm : forall (f : nat -> R) (l l' : list nat), Permutation l l' ->
  fold_right Rplus 0%R (map f l) = fold_right Rplus 0%R (map f l').
Proof.
  intros f l l' H; exact (Rsum_perm (map f l) (map f l') (Permutation_map f H)).
Qed.

(* ================================================================= *)
(*  4.  THE COPRIME DIVISOR SPLIT (the delicate Gauss keystone)       *)
(*                                                                    *)
(*  For coprime a, b, every divisor c of a*b factors as the product   *)
(*  of its gcd with a and its gcd with b:                             *)
(*     c = gcd(c,a) * gcd(c,b).                                       *)
(*  This is the heart of divisor-multiplicativity.  Proof by          *)
(*  antisymmetry of divisibility, each direction a Gauss argument:    *)
(*   - c | g*e :  writing c = c1*g, a = a1*g with gcd(c1,a1)=1         *)
(*       (Nat.gcd_div_gcd), c1 | a1*b so c1 | b (Nat.gauss), hence     *)
(*       c1 | gcd(c,b)=e and c = c1*g | g*e;                          *)
(*   - g*e | c :  g,e both divide c and are coprime (Nat.gauss).      *)
(* ================================================================= *)

Lemma split_divisor : forall a b c, Nat.gcd a b = 1 -> 1 <= a -> 1 <= b ->
  Nat.divide c (a*b) -> c = Nat.gcd c a * Nat.gcd c b.
Proof.
  intros a b c Hab Ha Hb Hc.
  assert (Hc1 : 1 <= c)
    by (destruct c as [|c']; [ destruct Hc as [k Hk]; simpl in Hk; nia | lia ]).
  set (g := Nat.gcd c a). set (e := Nat.gcd c b).
  assert (Hg1 : 1 <= g)
    by (unfold g; destruct (Nat.gcd c a) eqn:G; [ apply Nat.gcd_eq_0 in G; lia | lia ]).
  assert (Hgc : Nat.divide g c) by (unfold g; apply Nat.gcd_divide_l).
  assert (Hga : Nat.divide g a) by (unfold g; apply Nat.gcd_divide_r).
  assert (Hec : Nat.divide e c) by (unfold e; apply Nat.gcd_divide_l).
  assert (Heb : Nat.divide e b) by (unfold e; apply Nat.gcd_divide_r).
  assert (Hge : Nat.gcd g e = 1).
  { assert (H1 : Nat.divide (Nat.gcd g e) a)
      by (apply Nat.divide_trans with g; [ apply Nat.gcd_divide_l | exact Hga ]).
    assert (H2 : Nat.divide (Nat.gcd g e) b)
      by (apply Nat.divide_trans with e; [ apply Nat.gcd_divide_r | exact Heb ]).
    apply Nat.divide_1_r; rewrite <- Hab; apply Nat.gcd_greatest; assumption. }
  apply Nat.divide_antisym.
  - (* c | g*e *)
    destruct Hgc as [c1 Hc1eq]. destruct Hga as [a1 Ha1eq].
    assert (Hcop : Nat.gcd c1 a1 = 1).
    { assert (Hcd : c / g = c1) by (rewrite Hc1eq, Nat.div_mul by lia; reflexivity).
      assert (Had : a / g = a1) by (rewrite Ha1eq, Nat.div_mul by lia; reflexivity).
      rewrite <- Hcd, <- Had; apply Nat.gcd_div_gcd; [ lia | unfold g; reflexivity ]. }
    assert (Hc1ab : Nat.divide c1 (a1 * b)).
    { destruct Hc as [q Hq]. exists q.
      apply (Nat.mul_cancel_r _ _ g); [ lia | ].
      rewrite Ha1eq, Hc1eq in Hq; nia. }
    assert (Hc1b : Nat.divide c1 b) by (apply Nat.gauss with (m := a1); assumption).
    assert (Hc1e : Nat.divide c1 e)
      by (unfold e; apply Nat.gcd_greatest; [ exists g; rewrite Hc1eq; ring | exact Hc1b ]).
    destruct Hc1e as [m Hm]. exists m. rewrite Hm, Hc1eq; ring.
  - (* g*e | c *)
    destruct Hgc as [c1 Hc1eq].
    assert (Hediv : Nat.divide e c1)
      by (apply Nat.gauss with (m := g);
          [ replace (g * c1) with c by (rewrite Hc1eq; ring); exact Hec
          | rewrite Nat.gcd_comm; exact Hge ]).
    destruct Hediv as [m Hm]. exists m. rewrite Hc1eq, Hm; ring.
Qed.

(* ================================================================= *)
(*  5.  GCD HELPERS FOR THE PRODUCT MAP                              *)
(* ================================================================= *)

Lemma gcd_coprime_of_dvd : forall a b e,
  Nat.divide e b -> Nat.gcd a b = 1 -> Nat.gcd e a = 1.
Proof.
  intros a b e Heb Hab; apply Nat.divide_1_r; rewrite <- Hab.
  apply Nat.gcd_greatest;
    [ apply Nat.gcd_divide_r
    | apply Nat.divide_trans with e; [ apply Nat.gcd_divide_l | exact Heb ] ].
Qed.

(* gcd(d*e, a) = d  when d | a and gcd(e,a) = 1 *)
Lemma gcd_mul_coprime : forall a d e,
  Nat.divide d a -> Nat.gcd e a = 1 -> Nat.gcd (d*e) a = d.
Proof.
  intros a d e Hda Hea; apply Nat.divide_antisym.
  - (* gcd(d*e,a) | d, via Gauss (coprime to e) *)
    apply Nat.gauss with (m := e).
    + replace (e*d) with (d*e) by ring; apply Nat.gcd_divide_l.
    + assert (Hae : Nat.gcd a e = 1) by (rewrite Nat.gcd_comm; exact Hea).
      apply Nat.divide_1_r; rewrite <- Hae; apply Nat.gcd_greatest.
      * apply Nat.divide_trans with (Nat.gcd (d*e) a);
          [ apply Nat.gcd_divide_l | apply Nat.gcd_divide_r ].
      * apply Nat.gcd_divide_r.
  - apply Nat.gcd_greatest; [ exists e; ring | exact Hda ].
Qed.

(* ================================================================= *)
(*  6.  NoDup PLUMBING FOR list_prod                                 *)
(* ================================================================= *)

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

Lemma NoDup_list_prod : forall (A B : Type) (l1 : list A) (l2 : list B),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros A B l1 l2; induction l1 as [|x l1 IH]; intros H1 H2; simpl; [ constructor | ].
  rewrite NoDup_cons_iff in H1; destruct H1 as [Hx H1].
  apply NoDup_app.
  - apply NoDup_map_inj; [ intros u v _ _ Heq; injection Heq; auto | exact H2 ].
  - apply IH; [ exact H1 | exact H2 ].
  - intros p Hp1 Hp2.
    apply in_map_iff in Hp1; destruct Hp1 as [y1 [Hy1 _]]; subst p.
    apply in_prod_iff in Hp2; destruct Hp2 as [Hpx _]; contradiction.
Qed.

(* ================================================================= *)
(*  7.  THE DIVISOR-LIST BIJECTION AND dsum REINDEXING               *)
(* ================================================================= *)

(* the product map on divisor pairs is injective (coprime case) *)
Lemma prod_map_inj : forall a b, Nat.gcd a b = 1 -> 1 <= a -> 1 <= b ->
  forall de1 de2,
    In de1 (list_prod (divisors a) (divisors b)) ->
    In de2 (list_prod (divisors a) (divisors b)) ->
    fst de1 * snd de1 = fst de2 * snd de2 -> de1 = de2.
Proof.
  intros a b Hab Ha Hb [d1 e1] [d2 e2] Hin1 Hin2 Heq; simpl in Heq.
  apply in_prod_iff in Hin1; apply in_prod_iff in Hin2.
  destruct Hin1 as [Hd1 He1]; destruct Hin2 as [Hd2 He2].
  rewrite in_divisors in Hd1, He1, Hd2, He2.
  destruct Hd1 as [[Hd1a Hd1b] Hd1d]; destruct He1 as [[He1a He1b] He1d].
  destruct Hd2 as [[Hd2a Hd2b] Hd2d]; destruct He2 as [[He2a He2b] He2d].
  assert (Hc1 : Nat.gcd (d1*e1) a = d1)
    by (apply gcd_mul_coprime; [ exact Hd1d | apply gcd_coprime_of_dvd with b; assumption ]).
  assert (Hc2 : Nat.gcd (d2*e2) a = d2)
    by (apply gcd_mul_coprime; [ exact Hd2d | apply gcd_coprime_of_dvd with b; assumption ]).
  assert (Hdd : d1 = d2) by (rewrite <- Hc1, <- Hc2, Heq; reflexivity).
  assert (Hee : e1 = e2) by (apply (Nat.mul_cancel_l _ _ d1); [ lia | rewrite Hdd at 2; exact Heq ]).
  subst; reflexivity.
Qed.

Lemma divisors_prod_perm : forall a b, Nat.gcd a b = 1 -> 1 <= a -> 1 <= b ->
  Permutation (divisors (a*b))
              (map (fun de => fst de * snd de) (list_prod (divisors a) (divisors b))).
Proof.
  intros a b Hab Ha Hb; apply NoDup_Permutation.
  - apply divisors_nodup.
  - apply NoDup_map_inj;
      [ apply prod_map_inj; assumption
      | apply NoDup_list_prod; apply divisors_nodup ].
  - intro c; rewrite in_divisors; split.
    + intros [Hcr Hcd]; apply in_map_iff.
      exists (Nat.gcd c a, Nat.gcd c b); split; simpl.
      * symmetry; apply split_divisor; [ exact Hab | lia | lia | exact Hcd ].
      * apply in_prod_iff; split; rewrite in_divisors.
        -- split; [ split | apply Nat.gcd_divide_r ].
           ++ destruct (Nat.gcd c a) eqn:G; [ apply Nat.gcd_eq_0 in G; lia | lia ].
           ++ apply Nat.divide_pos_le; [ lia | apply Nat.gcd_divide_r ].
        -- split; [ split | apply Nat.gcd_divide_r ].
           ++ destruct (Nat.gcd c b) eqn:G; [ apply Nat.gcd_eq_0 in G; lia | lia ].
           ++ apply Nat.divide_pos_le; [ lia | apply Nat.gcd_divide_r ].
    + intro Hin; apply in_map_iff in Hin; destruct Hin as [[d e] [Hphi Hprod]]; simpl in Hphi.
      apply in_prod_iff in Hprod; destruct Hprod as [Hd He].
      rewrite in_divisors in Hd, He.
      destruct Hd as [[Hd1 Hd2] Hdd]; destruct He as [[He1 He2] Hed].
      subst c; split; [ nia | ].
      destruct Hdd as [da Hda]; destruct Hed as [eb Heb]; exists (da*eb); subst; ring.
Qed.

(* the divisor sum over a coprime product reindexes over the pair-product *)
Lemma dsum_prod : forall (f : nat -> R) a b, Nat.gcd a b = 1 -> 1 <= a -> 1 <= b ->
  dsum f (a*b)
  = fold_right Rplus 0%R
      (map (fun de => f (fst de * snd de)) (list_prod (divisors a) (divisors b))).
Proof.
  intros f a b Hab Ha Hb; unfold dsum.
  rewrite (dsum_perm f _ _ (divisors_prod_perm a b Hab Ha Hb)), map_map; reflexivity.
Qed.

(* ================================================================= *)
(*  8.  THE GLOBAL VON MANGOLDT FUNCTION Lambda                      *)
(* ================================================================= *)

(* Euclid for nprime *)
Lemma nprime_euclid : forall p a b,
  nprime p -> Nat.divide p (a*b) -> Nat.divide p a \/ Nat.divide p b.
Proof.
  intros p a b [Hp2 Hpd] Hpab.
  destruct (Nat.eq_dec (Nat.gcd p a) p) as [Hg|Hg].
  - left; rewrite <- Hg; apply Nat.gcd_divide_r.
  - right; apply Nat.gauss with (m := a); [ exact Hpab | ].
    destruct (Hpd (Nat.gcd p a) (Nat.gcd_divide_l _ _)) as [H1|Hp']; [ exact H1 | contradiction ].
Qed.

(* a prime dividing q^k equals q *)
Lemma prime_dvd_prime_pow : forall p q k,
  nprime p -> nprime q -> Nat.divide p (q^k) -> p = q.
Proof.
  intros p q k Hp Hq; induction k as [|k IH]; intro Hpk.
  - simpl in Hpk; apply Nat.divide_1_r in Hpk; destruct Hp as [Hp2 _]; lia.
  - simpl in Hpk; destruct (nprime_euclid p q (q^k) Hp Hpk) as [Hpq|Hpqk].
    + destruct Hq as [Hq2 Hqd]; destruct (Hqd p Hpq) as [H1|He];
        [ destruct Hp; lia | exact He ].
    + apply IH; exact Hpqk.
Qed.

(* prime-power test: is_pow p n = true  iff  n is a power of p *)
Fixpoint is_pow (fuel p n : nat) : bool :=
  match fuel with
  | O => false
  | S f => if Nat.eqb n 1 then true
           else if Nat.eqb (n mod p) 0 then is_pow f p (n / p) else false
  end.

Lemma is_pow_true_pow : forall fuel p n, 2 <= p -> is_pow fuel p n = true -> exists k, n = p^k.
Proof.
  induction fuel as [|f IH]; intros p n Hp H; simpl in H; [ discriminate | ].
  destruct (Nat.eqb n 1) eqn:E1.
  - apply Nat.eqb_eq in E1; exists 0; simpl; lia.
  - destruct (Nat.eqb (n mod p) 0) eqn:E2; [ | discriminate ].
    apply Nat.eqb_eq, Nat.Lcm0.mod_divide in E2.
    destruct (IH p (n/p) Hp H) as [k Hk].
    exists (S k); destruct E2 as [q Hq].
    rewrite Hq, Nat.div_mul in Hk by lia; rewrite Hq, Hk; simpl; ring.
Qed.

(* the global von Mangoldt function.  spf 1 = 1 and ln (INR 1) = 0, so    *)
(* Lambda 1 = 0 needs no special case.                                   *)
Definition Lam (n : nat) : R :=
  if is_pow n (spf n) n then ln (INR (spf n)) else 0%R.

Lemma Lam_1 : Lam 1 = 0%R.
Proof.
  unfold Lam.
  replace (is_pow 1 (spf 1) 1) with true by reflexivity.
  replace (spf 1) with 1 by reflexivity.
  replace (INR 1) with 1%R by (simpl; ring); rewrite ln_1; reflexivity.
Qed.

(* Lambda vanishes on a coprime product of two non-units (two distinct     *)
(* primes, so not a prime power)                                          *)
Lemma Lam_mul_zero : forall d e,
  2 <= d -> 2 <= e -> Nat.gcd d e = 1 -> Lam (d*e) = 0%R.
Proof.
  intros d e Hd He Hde; unfold Lam.
  destruct (is_pow (d*e) (spf (d*e)) (d*e)) eqn:E; [ exfalso | reflexivity ].
  assert (Hde2 : 2 <= d*e) by nia.
  assert (Hq2 : 2 <= spf (d*e)) by (apply spf_ge2; exact Hde2).
  destruct (is_pow_true_pow (d*e) (spf (d*e)) (d*e) Hq2 E) as [k Hk].
  set (q := spf (d*e)) in *.
  assert (Hqp : nprime q) by (unfold q; apply spf_nprime; exact Hde2).
  (* spf d = q and spf e = q *)
  assert (Hdq : spf d = q).
  { apply (prime_dvd_prime_pow (spf d) q k); [ apply spf_nprime; lia | exact Hqp | ].
    rewrite <- Hk. apply Nat.divide_trans with d; [ apply spf_divides; lia | exists e; ring ]. }
  assert (Heq : spf e = q).
  { apply (prime_dvd_prime_pow (spf e) q k); [ apply spf_nprime; lia | exact Hqp | ].
    rewrite <- Hk. apply Nat.divide_trans with e; [ apply spf_divides; lia | exists d; ring ]. }
  (* q divides gcd d e = 1, contradiction *)
  assert (Hq1 : Nat.divide q 1).
  { rewrite <- Hde. apply Nat.gcd_greatest.
    - rewrite <- Hdq; apply spf_divides; lia.
    - rewrite <- Heq; apply spf_divides; lia. }
  apply Nat.divide_1_r in Hq1; destruct Hqp as [Hq2' _]; lia.
Qed.

(* the per-pair collapse: for coprime d,e, Lambda(d*e) is Lambda of        *)
(* whichever factor is >1 (or 0 if both are)                              *)
Lemma Lam_collapse : forall d e, Nat.gcd d e = 1 -> 1 <= d -> 1 <= e ->
  Lam (d*e) = ((if Nat.eqb d 1 then Lam e else 0) + (if Nat.eqb e 1 then Lam d else 0))%R.
Proof.
  intros d e Hde Hd He.
  destruct (Nat.eq_dec d 1) as [->|Hd1].
  - rewrite Nat.mul_1_l, Nat.eqb_refl.
    destruct (Nat.eqb e 1) eqn:Ee; [ apply Nat.eqb_eq in Ee; subst e; rewrite Lam_1 | ]; lra.
  - destruct (Nat.eq_dec e 1) as [->|He1].
    + rewrite Nat.mul_1_r.
      destruct (Nat.eqb d 1) eqn:Ed; [ apply Nat.eqb_eq in Ed; lia | ].
      rewrite Nat.eqb_refl; lra.
    + rewrite Lam_mul_zero by (try lia; exact Hde).
      destruct (Nat.eqb d 1) eqn:Ed; [ apply Nat.eqb_eq in Ed; lia | ].
      destruct (Nat.eqb e 1) eqn:Ee; [ apply Nat.eqb_eq in Ee; lia | ]. lra.
Qed.

(* ================================================================= *)
(*  9.  THE dsum-LEVEL COLLAPSE (pure sum manipulation)              *)
(* ================================================================= *)

Lemma Rsum_app : forall l1 l2 : list R,
  fold_right Rplus 0%R (l1 ++ l2) = (fold_right Rplus 0%R l1 + fold_right Rplus 0%R l2)%R.
Proof. induction l1 as [|x l1 IH]; intro l2; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma Rsum_plus : forall (A : Type) (f g : A -> R) (l : list A),
  fold_right Rplus 0%R (map (fun x => (f x + g x)%R) l)
  = (fold_right Rplus 0%R (map f l) + fold_right Rplus 0%R (map g l))%R.
Proof. intros A f g; induction l as [|x l IH]; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma Rsum_pull_if : forall (bb : bool) (h : nat -> R) (l : list nat),
  fold_right Rplus 0%R (map (fun e => if bb then h e else 0%R) l)
  = (if bb then fold_right Rplus 0%R (map h l) else 0%R).
Proof.
  intros bb h l; induction l as [|x l IH]; simpl;
    [ destruct bb; reflexivity | rewrite IH; destruct bb; simpl; ring ].
Qed.

Lemma Rsum_if1_notin : forall L B, ~ In 1 L ->
  fold_right Rplus 0%R (map (fun d => if Nat.eqb d 1 then B else 0%R) L) = 0%R.
Proof.
  intros L B; induction L as [|x L IH]; intro Hnin; simpl; [ reflexivity | ].
  destruct (Nat.eqb x 1) eqn:E.
  - apply Nat.eqb_eq in E; subst x; exfalso; apply Hnin; left; reflexivity.
  - rewrite IH; [ ring | intro Hin; apply Hnin; right; exact Hin ].
Qed.

Lemma Rsum_if1 : forall L B, NoDup L -> In 1 L ->
  fold_right Rplus 0%R (map (fun d => if Nat.eqb d 1 then B else 0%R) L) = B.
Proof.
  intros L B; induction L as [|x L IH]; intros Hnd Hin; [ destruct Hin | ].
  rewrite NoDup_cons_iff in Hnd; destruct Hnd as [Hnx Hnd].
  simpl; destruct (Nat.eqb x 1) eqn:E.
  - apply Nat.eqb_eq in E; subst x; rewrite (Rsum_if1_notin L B Hnx); ring.
  - destruct Hin as [Hx|Hin];
      [ apply Nat.eqb_neq in E; contradiction | rewrite (IH Hnd Hin); ring ].
Qed.

Lemma Fubini_list_prod : forall (g : nat -> nat -> R) (l1 l2 : list nat),
  fold_right Rplus 0%R (map (fun de => g (fst de) (snd de)) (list_prod l1 l2))
  = fold_right Rplus 0%R (map (fun d => fold_right Rplus 0%R (map (g d) l2)) l1).
Proof.
  intros g l1 l2; induction l1 as [|x l1 IH]; simpl; [ reflexivity | ].
  rewrite map_app, Rsum_app, map_map, IH.
  f_equal; apply f_equal, map_ext; intro y; reflexivity.
Qed.

Lemma in_1_divisors : forall n, 1 <= n -> In 1 (divisors n).
Proof. intros n Hn; apply in_divisors; split; [ lia | apply Nat.divide_1_l ]. Qed.

(* THE COLLAPSE: dsum Lambda is additive over coprime products *)
Theorem dsum_mult : forall a b, Nat.gcd a b = 1 -> 1 <= a -> 1 <= b ->
  dsum Lam (a*b) = (dsum Lam a + dsum Lam b)%R.
Proof.
  intros a b Hab Ha Hb.
  rewrite (dsum_prod Lam a b Hab Ha Hb).
  transitivity (fold_right Rplus 0%R
     (map (fun de => ((if Nat.eqb (fst de) 1 then Lam (snd de) else 0)
                      + (if Nat.eqb (snd de) 1 then Lam (fst de) else 0))%R)
          (list_prod (divisors a) (divisors b)))).
  - f_equal; apply map_ext_in; intros [d e] Hin.
    apply in_prod_iff in Hin; destruct Hin as [Hd He].
    rewrite in_divisors in Hd, He.
    destruct Hd as [[Hd1 _] Hdd]; destruct He as [[He1 _] Hed].
    assert (Hcop : Nat.gcd d e = 1).
    { apply Nat.divide_1_r; rewrite <- Hab; apply Nat.gcd_greatest;
        [ apply Nat.divide_trans with d; [ apply Nat.gcd_divide_l | exact Hdd ]
        | apply Nat.divide_trans with e; [ apply Nat.gcd_divide_r | exact Hed ] ]. }
    simpl; apply Lam_collapse; assumption.
  - rewrite Rsum_plus.
    rewrite (Fubini_list_prod (fun d e => if Nat.eqb d 1 then Lam e else 0%R)).
    rewrite (Fubini_list_prod (fun d e => if Nat.eqb e 1 then Lam d else 0%R)).
    (* first term: inner = if d=1 then dsum Lam b else 0, outer picks d=1 *)
    erewrite map_ext with
      (f := fun d => fold_right Rplus 0%R (map (fun e => if Nat.eqb d 1 then Lam e else 0%R) (divisors b))).
    2:{ intro d; rewrite (Rsum_pull_if (Nat.eqb d 1) Lam (divisors b)); reflexivity. }
    (* second term: inner = Lam d (picks e=1 over div b) *)
    erewrite map_ext with
      (f := fun d => fold_right Rplus 0%R (map (fun e => if Nat.eqb e 1 then Lam d else 0%R) (divisors b))).
    2:{ intro d; rewrite (Rsum_if1 (divisors b) (Lam d) (divisors_nodup b) (in_1_divisors b Hb));
        reflexivity. }
    (* now: fold(map (fun d => if d=1 then dsum Lam b else 0) div a)
           + fold(map Lam div a)  =  dsum Lam a + dsum Lam b *)
    unfold dsum.
    rewrite (Rsum_if1 (divisors a) (fold_right Rplus 0%R (map Lam (divisors b)))
               (divisors_nodup a) (in_1_divisors a Ha)).
    ring.
Qed.

(* ================================================================= *)
(*  10.  PRIME-POWER DIVISORS AND THE PRIME-POWER BASE               *)
(* ================================================================= *)

(* divisors of a prime power are exactly its powers *)
Lemma dvd_prime_pow : forall p k d,
  nprime p -> Nat.divide d (p^k) -> exists j, (j <= k)%nat /\ d = p^j.
Proof.
  intros p k; induction k as [|k IH]; intros d Hp Hd.
  - simpl in Hd; apply Nat.divide_1_r in Hd; exists 0; simpl; auto.
  - simpl in Hd.
    destruct (Nat.eq_dec (Nat.gcd d p) p) as [Hg|Hg].
    + assert (Hpd : Nat.divide p d) by (rewrite <- Hg; apply Nat.gcd_divide_l).
      destruct Hpd as [d' Hd'].
      assert (Hd'pk : Nat.divide d' (p^k)).
      { destruct Hd as [c Hc]. exists c.
        apply (Nat.mul_cancel_r _ _ p); [ destruct Hp; lia | ].
        rewrite Hd' in Hc; nia. }
      destruct (IH d' Hp Hd'pk) as [j [Hj Hdj]].
      exists (S j); split; [ lia | rewrite Hd', Hdj; simpl; ring ].
    + assert (Hgcd : Nat.gcd d p = 1).
      { destruct Hp as [Hp2 Hpd']; destruct (Hpd' (Nat.gcd d p) (Nat.gcd_divide_r _ _)) as [H1|Hp'];
          [ exact H1 | contradiction ]. }
      assert (Hdpk : Nat.divide d (p^k))
        by (apply Nat.gauss with (m := p); [ exact Hd | exact Hgcd ]).
      destruct (IH d Hp Hdpk) as [j [Hj Hdj]]; exists j; split; [ lia | exact Hdj ].
Qed.

Lemma spf_prime_pow : forall p j, nprime p -> 1 <= j -> spf (p^j) = p.
Proof.
  intros p j Hp Hj; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hpj2 : 2 <= p^j)
    by (apply Nat.le_trans with (p^1); [ rewrite Nat.pow_1_r; exact Hp2 | apply Nat.pow_le_mono_r; lia ]).
  assert (Hpn : Nat.divide p (p^j)).
  { assert (Hpj : p^j = p * p^(j-1)) by (replace j with (S (j-1)) at 1 by lia; apply Nat.pow_succ_r').
    exists (p^(j-1)); rewrite Hpj; ring. }
  assert (Hge : 2 <= spf (p^j)) by (apply spf_ge2; exact Hpj2).
  destruct (dvd_prime_pow p j (spf (p^j)) Hp (spf_divides _ Hpj2)) as [i [Hi Hspf]].
  assert (Hle : spf (p^j) <= p).
  { destruct (le_gt_dec (spf (p^j)) p) as [Hle|Hgt]; [ exact Hle | exfalso ].
    apply (spf_least (p^j) p Hpj2 Hp2 Hgt); exact Hpn. }
  assert (Hgep : p <= spf (p^j)).
  { rewrite Hspf; destruct i as [|i'].
    - rewrite Hspf in Hge; simpl in Hge; lia.
    - apply Nat.le_trans with (p^1); [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ]. }
  lia.
Qed.

Lemma is_pow_pow_true : forall fuel p j, 2 <= p -> (j < fuel)%nat -> is_pow fuel p (p^j) = true.
Proof.
  induction fuel as [|f IH]; intros p j Hp Hj; [ lia | ].
  simpl; destruct (Nat.eqb (p^j) 1) eqn:E1; [ reflexivity | ].
  assert (Hj1 : 1 <= j).
  { destruct j; [ simpl in E1; discriminate | lia ]. }
  assert (Hpj : p^j = p * p^(j-1)) by (replace j with (S (j-1)) at 1 by lia; apply Nat.pow_succ_r').
  assert (Hmod : (p^j) mod p = 0) by (apply Nat.Lcm0.mod_divide; exists (p^(j-1)); rewrite Hpj; ring).
  assert (Hb : (Nat.eqb (p^j mod p) 0) = true) by (apply Nat.eqb_eq; exact Hmod).
  rewrite Hb.
  replace (p^j / p) with (p^(j-1))
    by (rewrite Hpj, Nat.mul_comm, Nat.div_mul by lia; reflexivity).
  apply IH; [ exact Hp | lia ].
Qed.

Lemma Lam_prime_pow : forall p j, nprime p -> 1 <= j -> Lam (p^j) = ln (INR p).
Proof.
  intros p j Hp Hj; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hjlt : (j < p^j)%nat).
  { assert (j < 2^j)%nat by (clear; induction j as [|j IHj]; simpl; lia).
    assert (2^j <= p^j)%nat by (apply Nat.pow_le_mono_l; lia). lia. }
  unfold Lam.
  rewrite (spf_prime_pow p j Hp Hj), (is_pow_pow_true (p^j) p j Hp2 Hjlt); reflexivity.
Qed.

Lemma divisors_primepow : forall p k, nprime p ->
  Permutation (divisors (p^k)) (map (fun j => p^j) (seq 0 (S k))).
Proof.
  intros p k Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  apply NoDup_Permutation.
  - apply divisors_nodup.
  - apply NoDup_map_inj;
      [ intros x y _ _ Hexy; apply Nat.pow_inj_r with p; [ lia | exact Hexy ] | apply seq_NoDup ].
  - intro d; rewrite in_divisors; split.
    + intros [_ Hdd].
      destruct (dvd_prime_pow p k d Hp Hdd) as [j [Hj Hdj]].
      apply in_map_iff; exists j; split; [ symmetry; exact Hdj | apply in_seq; lia ].
    + intro Hin; apply in_map_iff in Hin; destruct Hin as [j [Hdj Hjin]].
      apply in_seq in Hjin; subst d; split.
      * split.
        -- rewrite <- (Nat.pow_1_l j); apply Nat.pow_le_mono_l; lia.
        -- apply Nat.pow_le_mono_r; lia.
      * exists (p^(k-j)); rewrite <- Nat.pow_add_r; f_equal; lia.
Qed.

Lemma pow_pos_R : forall p k, 1 <= p -> (0 < INR (p^k))%R.
Proof.
  intros p k Hp; apply lt_0_INR.
  assert (1 <= p^k)%nat by (rewrite <- (Nat.pow_1_l k); apply Nat.pow_le_mono_l; lia); lia.
Qed.

Lemma sum_pow_Lam : forall p k, nprime p ->
  fold_right Rplus 0%R (map (fun j => Lam (p^j)) (seq 0 (S k))) = ln (INR (p^k)).
Proof.
  intros p k Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  induction k as [|k IH].
  - cbn [seq map fold_right]; rewrite Nat.pow_0_r, Lam_1.
    replace (INR 1) with 1%R by (simpl; ring); rewrite ln_1; ring.
  - rewrite seq_S, map_app, Rsum_app, IH; cbn [map fold_right]; rewrite Nat.add_0_l.
    rewrite (Lam_prime_pow p (S k) Hp) by lia.
    replace (p ^ S k) with (p * p^k) by (rewrite Nat.pow_succ_r'; reflexivity).
    rewrite mult_INR, ln_mult; [ ring | apply lt_0_INR; lia | apply pow_pos_R; lia ].
Qed.

Lemma dsum_primepow : forall p k, nprime p -> dsum Lam (p^k) = ln (INR (p^k)).
Proof.
  intros p k Hp; unfold dsum.
  rewrite (dsum_perm Lam _ _ (divisors_primepow p k Hp)), map_map.
  apply sum_pow_Lam; exact Hp.
Qed.

(* ================================================================= *)
(*  11.  p-ADIC VALUATION AND THE ASSEMBLY                           *)
(* ================================================================= *)

Lemma coprime_ppow_pfree : forall p a m,
  nprime p -> ~ Nat.divide p m -> Nat.gcd (p^a) m = 1.
Proof.
  intros p a m Hp Hpm.
  destruct (dvd_prime_pow p a (Nat.gcd (p^a) m) Hp (Nat.gcd_divide_l _ _)) as [j [Hj Hg]].
  destruct j as [|j']; [ simpl in Hg; exact Hg | exfalso ].
  apply Hpm; apply Nat.divide_trans with (Nat.gcd (p^a) m); [ | apply Nat.gcd_divide_r ].
  rewrite Hg; exists (p^j'); simpl; ring.
Qed.

Lemma pval_fuel : forall fuel p n, 2 <= p -> 1 <= n -> (n <= fuel)%nat ->
  exists a m, n = p^a * m /\ ~ Nat.divide p m /\ 1 <= m.
Proof.
  induction fuel as [|f IH]; intros p n Hp Hn Hnf; [ lia | ].
  destruct (Nat.eq_dec (n mod p) 0) as [Hmod|Hmod].
  - assert (Hpn : Nat.divide p n) by (apply Nat.Lcm0.mod_divide; exact Hmod).
    destruct Hpn as [n' Hn'].
    assert (Hn'1 : 1 <= n') by nia.
    assert (Hn'f : (n' <= f)%nat) by nia.
    destruct (IH p n' Hp Hn'1 Hn'f) as [a [m [Heq [Hnd Hm]]]].
    exists (S a), m; split; [ rewrite Hn', Heq; simpl; ring | split; assumption ].
  - exists 0, n; split; [ simpl; lia | split; [ | exact Hn ] ].
    intro Hd; apply Hmod, Nat.Lcm0.mod_divide; exact Hd.
Qed.

(* THE GLOBAL VON MANGOLDT IDENTITY *)
Theorem vonmangoldt_identity : forall n, 1 <= n -> dsum Lam n = ln (INR n).
Proof.
  intro n; induction n as [n IH] using (well_founded_induction lt_wf); intro Hn.
  destruct (Nat.eq_dec n 1) as [->|Hn1].
  - unfold dsum; replace (divisors 1) with (1 :: nil) by reflexivity.
    cbn [map fold_right]; rewrite Lam_1.
    replace (INR 1) with 1%R by (simpl; ring); rewrite ln_1; ring.
  - assert (Hn2 : 2 <= n) by lia.
    set (p := spf n).
    assert (Hp : nprime p) by (apply spf_nprime; exact Hn2).
    assert (Hp2 : 2 <= p) by (destruct Hp; lia).
    assert (Hpn : Nat.divide p n) by (apply spf_divides; exact Hn2).
    destruct (pval_fuel n p n Hp2 Hn (le_n n)) as [a [m [Heq [Hpm Hm]]]].
    assert (Ha1 : 1 <= a).
    { destruct a as [|a']; [ exfalso | lia ].
      apply Hpm.
      assert (Hnm : m = n) by (rewrite Heq; simpl; lia).
      rewrite Hnm; exact Hpn. }
    assert (Hcop : Nat.gcd (p^a) m = 1) by (apply coprime_ppow_pfree; assumption).
    assert (Hpa1 : 1 <= p^a)
      by (rewrite <- (Nat.pow_1_l a); apply Nat.pow_le_mono_l; lia).
    assert (Hpa2 : 2 <= p^a)
      by (apply Nat.le_trans with (p^1); [ rewrite Nat.pow_1_r; lia | apply Nat.pow_le_mono_r; lia ]).
    assert (Hmlt : (m < n)%nat) by (rewrite Heq; nia).
    rewrite Heq, (dsum_mult (p^a) m Hcop Hpa1 Hm),
            (dsum_primepow p a Hp), (IH m Hmlt Hm).
    rewrite mult_INR, ln_mult; [ reflexivity | apply pow_pos_R; lia | apply lt_0_INR; lia ].
Qed.

Print Assumptions vonmangoldt_identity.

(* ================================================================= *)
(*  END VonMangoldtGlobal.v -- sum_{d|n} Lambda(d) = log n            *)
(*  spf (smallest prime factor, proved prime), the divisor sum dsum,   *)
(*  and its permutation-invariance -- the foundation for Lambda and    *)
(*  the identity sum_{d|n} Lambda(d) = log n.                          *)
(* ================================================================= *)
