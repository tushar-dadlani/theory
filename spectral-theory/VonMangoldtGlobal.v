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

Print Assumptions dsum_prod.

(* ================================================================= *)
(*  END VonMangoldtGlobal.v (checkpoint A + keystone + divisor bij.) *)
(*  spf (smallest prime factor, proved prime), the divisor sum dsum,   *)
(*  and its permutation-invariance -- the foundation for Lambda and    *)
(*  the identity sum_{d|n} Lambda(d) = log n.                          *)
(* ================================================================= *)
