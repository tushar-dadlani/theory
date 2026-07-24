(* ================================================================= *)
(*  ReciprocityCount.v                                               *)
(*                                                                    *)
(*  THE LATTICE-POINT COUNT behind quadratic reciprocity:            *)
(*                                                                    *)
(*    sum_{k=1}^{(p-1)/2} floor(k*q/p) + sum_{j=1}^{(q-1)/2}          *)
(*        floor(j*p/q)  =  ((p-1)/2) * ((q-1)/2),                     *)
(*                                                                    *)
(*  for distinct odd primes p, q.  Pure elementary counting: the      *)
(*  lattice points (k,j) in the rectangle [1,(p-1)/2]x[1,(q-1)/2]     *)
(*  split into those below (p*j < q*k) and above (q*k < p*j) the      *)
(*  line q*x = p*y (no point ON it, since p does not divide q*k), and *)
(*  each row/column count is a floor.  AXIOM-FREE.                    *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation.
Require Import ZmodPStar LegendreSymbol.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(*  §1  generic list helpers                                         *)
(* ================================================================= *)

Lemma NoDup_map_inj : forall (X Y:Type)(f:X->Y)(l:list X),
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros X Y f l; induction l as [|x l IH]; intros Hinj HND; simpl; [ constructor | ].
  inversion HND as [|u v Hnin HND' Heq]; subst; constructor.
  - rewrite in_map_iff; intros [y [Hy Hiny]].
    assert (E : x = y) by (apply (Hinj x y); [left; reflexivity | right; exact Hiny | symmetry; exact Hy]).
    rewrite E in Hnin; contradiction.
  - apply IH; [ intros a b Ha Hb; apply Hinj; right; assumption | exact HND' ].
Qed.

Lemma NoDup_list_prod : forall (X Y:Type)(l1:list X)(l2:list Y),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros X Y l1 l2; induction l1 as [|a l1 IH]; intros H1 H2; simpl; [ constructor | ].
  inversion H1 as [|u v Hnin H1' Heq]; subst; apply NoDup_app.
  - apply NoDup_map_inj; [ intros p r _ _ E; injection E; auto | exact H2 ].
  - apply IH; [ exact H1' | exact H2 ].
  - intros ab Hin1 Hin2; destruct ab as [x y].
    rewrite in_map_iff in Hin1; destruct Hin1 as [z [Ez _]]; injection Ez as Ex Ey; subst.
    apply in_prod_iff in Hin2; destruct Hin2 as [Hain _]; contradiction.
Qed.

Lemma length_list_prod : forall (X Y:Type)(l1:list X)(l2:list Y),
  length (list_prod l1 l2) = length l1 * length l2.
Proof.
  intros X Y l1 l2; induction l1 as [|a l1 IH]; [ reflexivity | ].
  simpl; rewrite length_app, length_map, IH; reflexivity.
Qed.

Lemma filter_ext_in : forall (A:Type)(f g:A->bool) l,
  (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intros A f g l; induction l as [|a l IH]; intro H; [ reflexivity | ].
  simpl; rewrite (H a (or_introl eq_refl)), (IH (fun x Hx => H x (or_intror Hx))); reflexivity.
Qed.

Lemma filter_map_comm : forall (A B:Type)(f:A->B)(g:B->bool) l,
  filter g (map f l) = map f (filter (fun x => g (f x)) l).
Proof.
  intros A B f g l; induction l as [|a l IH]; [ reflexivity | ].
  simpl; destruct (g (f a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma Permutation_filter : forall (A:Type)(g:A->bool) l l',
  Permutation l l' -> Permutation (filter g l) (filter g l').
Proof.
  intros A g l l' H; induction H; simpl.
  - constructor.
  - destruct (g x); [ constructor | ]; assumption.
  - destruct (g x), (g y); try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* count of a 2-variable predicate over a product = sum of the row counts *)
Lemma count_list_prod : forall (A B:Type)(g:A*B->bool) l1 l2,
  length (filter g (list_prod l1 l2))
  = fold_right Nat.add 0 (map (fun k => length (filter (fun j => g (k, j)) l2)) l1).
Proof.
  intros A B g l1 l2; induction l1 as [|k l1 IH]; [ reflexivity | ].
  simpl list_prod; rewrite filter_app, length_app, IH; simpl map; simpl fold_right; f_equal.
  rewrite filter_map_comm, length_map; reflexivity.
Qed.

(* the transpose bijection preserves the count *)
Lemma count_transpose : forall (A B:Type)(g:A*B->bool) l1 l2, NoDup l1 -> NoDup l2 ->
  length (filter g (list_prod l1 l2))
  = length (filter (fun jk => g (snd jk, fst jk)) (list_prod l2 l1)).
Proof.
  intros A B g l1 l2 H1 H2.
  transitivity (length (filter g (map (fun jk : B*A => (snd jk, fst jk)) (list_prod l2 l1)))).
  - apply Permutation_length, Permutation_filter, NoDup_Permutation.
    + apply NoDup_list_prod; assumption.
    + apply NoDup_map_inj; [ intros [x y] [x' y'] _ _ E; cbn in E; injection E; intros; subst; reflexivity
                           | apply NoDup_list_prod; assumption ].
    + intros [a b]; rewrite in_prod_iff, in_map_iff; split.
      * intros [Ha Hb]; exists (b, a); cbn; split; [ reflexivity | apply in_prod_iff; split; assumption ].
      * intros [[x y] [E Hin]]; cbn in E; injection E; intros; subst;
          apply in_prod_iff in Hin; tauto.
  - rewrite filter_map_comm, length_map; reflexivity.
Qed.

Lemma count_le : forall m n, length (filter (fun j => j <=? m) (seq 1 n)) = Nat.min m n.
Proof.
  intros m n; induction n as [|n IH]; [ simpl; rewrite Nat.min_0_r; reflexivity | ].
  rewrite seq_S, filter_app, length_app, IH; cbn [filter length].
  destruct (1 + n <=? m) eqn:E; cbn [length].
  - apply Nat.leb_le in E.
    rewrite (Nat.min_r m n) by lia; rewrite (Nat.min_r m (S n)) by lia; lia.
  - apply Nat.leb_gt in E.
    rewrite (Nat.min_l m n) by lia; rewrite (Nat.min_l m (S n)) by lia; lia.
Qed.

(* ================================================================= *)
(*  §2  the row count is a floor                                     *)
(* ================================================================= *)

Lemma hlf_lt : forall p, hlf p <= p - 1.
Proof. intro p; unfold hlf; apply Nat.Div0.div_le_upper_bound; lia. Qed.

(* distinct primes p, q, prime p, k in [1,(p-1)/2]  =>  p does not divide q*k *)
Lemma p_ndvd : forall p q k, prime (Z.of_nat p) -> prime (Z.of_nat q) -> p <> q ->
  1 <= k <= hlf p -> ~ Nat.divide p (q * k).
Proof.
  intros p q k Hp Hq Hpq Hk Hd.
  pose proof (prime_ge_2 _ Hp) as Hp2; pose proof (prime_ge_2 _ Hq) as Hq2.
  pose proof (hlf_lt p) as Hhlf.
  destruct (prime_mult_nat p q k Hp Hd) as [H|H].
  - apply Hpq; apply Nat2Z.inj.
    assert (Hdz : (Z.of_nat p | Z.of_nat q))
      by (destruct H as [c Hc]; exists (Z.of_nat c); rewrite Hc, Nat2Z.inj_mul; ring).
    destruct (prime_divisors (Z.of_nat q) Hq (Z.of_nat p) Hdz) as [E|[E|[E|E]]]; lia.
  - apply (unit_not_div p k ltac:(lia)); exact H.
Qed.

(* p*j < q*k  <->  j <= floor(q*k/p) *)
Lemma pred_row_eq : forall p q k j, 2 <= p -> ~ Nat.divide p (q * k) ->
  (p * j <? q * k) = (j <=? (q * k) / p).
Proof.
  intros p q k j Hp Hnd.
  pose proof (Nat.div_mod_eq (q * k) p) as Hdm.
  pose proof (Nat.mod_upper_bound (q * k) p ltac:(lia)) as Hmod.
  assert (Hr : (q * k) mod p <> 0) by (intro E; apply Hnd, Nat.Lcm0.mod_divide; exact E).
  apply Bool.eq_iff_eq_true; rewrite Nat.ltb_lt, Nat.leb_le; split; intro; nia.
Qed.

(* floor(q*k/p) <= (q-1)/2   for odd primes and k <= (p-1)/2 *)
Lemma D_bound : forall p q k, p mod 2 = 1 -> q mod 2 = 1 -> 2 <= p -> 2 <= q ->
  1 <= k <= hlf p -> (q * k) / p <= hlf q.
Proof.
  intros p q k Hpo Hqo Hp2 Hq2 Hk.
  pose proof (two_hlf p Hpo Hp2) as HHp; pose proof (two_hlf q Hqo Hq2) as HHq.
  pose proof (Nat.div_mod_eq (q * k) p) as Hdm.
  pose proof (Nat.mod_upper_bound (q * k) p ltac:(lia)) as Hmod.
  nia.
Qed.

(* THE ROW COUNT *)
Lemma count_row : forall p q k,
  prime (Z.of_nat p) -> prime (Z.of_nat q) -> p <> q -> p mod 2 = 1 -> q mod 2 = 1 ->
  1 <= k <= hlf p ->
  length (filter (fun j => p * j <? q * k) (seq 1 (hlf q))) = (k * q) / p.
Proof.
  intros p q k Hp Hq Hpq Hpo Hqo Hk.
  pose proof (prime_ge_2 _ Hp); pose proof (prime_ge_2 _ Hq).
  rewrite (filter_ext_in nat (fun j => p * j <? q * k) (fun j => j <=? (q * k) / p)
             (seq 1 (hlf q))).
  2:{ intros j _; apply pred_row_eq; [ lia | apply (p_ndvd p q k); assumption ]. }
  rewrite count_le, Nat.min_l by (apply D_bound; try assumption; lia).
  rewrite Nat.mul_comm; reflexivity.
Qed.

(* ================================================================= *)
(*  §3  the lattice-point count                                      *)
(* ================================================================= *)

Definition fsum (p q : nat) : nat :=
  fold_right Nat.add 0 (map (fun k => (k * q) / p) (seq 1 (hlf p))).

Section Recip.

Variable p q : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hq : prime (Z.of_nat q).
Hypothesis Hpq : p <> q.
Hypothesis Hpo : p mod 2 = 1.
Hypothesis Hqo : q mod 2 = 1.

Notation box := (list_prod (seq 1 (hlf p)) (seq 1 (hlf q))).
Notation below := (fun kj : nat*nat => p * (snd kj) <? q * (fst kj)).

(* the "below the diagonal" count = fsum p q *)
Lemma below_count : length (filter below box) = fsum p q.
Proof.
  unfold fsum; rewrite count_list_prod; f_equal; apply map_ext_in.
  intros k Hk; apply in_seq in Hk; cbn [fst snd].
  apply count_row; [ exact Hp | exact Hq | exact Hpq | exact Hpo | exact Hqo | lia ].
Qed.

(* the "above the diagonal" count = fsum q p (transpose the box) *)
Lemma above_count : length (filter (fun kj => q * (fst kj) <? p * (snd kj)) box) = fsum q p.
Proof.
  rewrite (count_transpose _ _ _ (seq 1 (hlf p)) (seq 1 (hlf q))) by apply seq_NoDup.
  unfold fsum; rewrite count_list_prod; f_equal; apply map_ext_in.
  intros j Hj; apply in_seq in Hj; cbn [fst snd].
  apply count_row; [ exact Hq | exact Hp | (intro E; apply Hpq; symmetry; exact E)
                   | exact Hqo | exact Hpo | lia ].
Qed.

(* below and above partition the box (no lattice point on the diagonal) *)
Lemma above_is_negb : forall kj, In kj box -> (q * (fst kj) <? p * (snd kj)) = negb (below kj).
Proof.
  intros [k j] Hin; apply in_prod_iff in Hin; destruct Hin as [Hk Hj];
    apply in_seq in Hk; apply in_seq in Hj; cbn [fst snd].
  assert (Hnd : ~ Nat.divide p (q * k)) by (apply (p_ndvd p q k); [ exact Hp | exact Hq | exact Hpq | lia ]).
  assert (Hne : p * j <> q * k).
  { intro E; apply Hnd; exists j; rewrite <- E; ring. }
  apply Bool.eq_iff_eq_true; rewrite Nat.ltb_lt, Bool.negb_true_iff, Nat.ltb_ge; lia.
Qed.

Theorem reciprocity_count : fsum p q + fsum q p = hlf p * hlf q.
Proof.
  rewrite <- below_count, <- above_count.
  rewrite (filter_ext_in (nat*nat) (fun kj => q * (fst kj) <? p * (snd kj))
             (fun kj => negb (below kj)) box) by (exact above_is_negb).
  pose proof (filter_length below box) as HL.
  rewrite length_list_prod, !length_seq in HL; lia.
Qed.

End Recip.

Print Assumptions reciprocity_count.

(* ================================================================= *)
(*  END ReciprocityCount.v                                           *)
(*  The lattice-point count sum floor(k*q/p) + sum floor(j*p/q) =     *)
(*  ((p-1)/2)*((q-1)/2) for distinct odd primes p, q, by splitting    *)
(*  the rectangle of lattice points across the line q*x = p*y (no     *)
(*  point on it since p does not divide q*k).  Closed under the       *)
(*  global context (axiom-free).                                     *)
(* ================================================================= *)
