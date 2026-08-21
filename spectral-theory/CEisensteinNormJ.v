(* ================================================================= *)
(*  CEisensteinNormJ.v  —  N(J) = p  for the Jacobi sum.               *)
(*                                                                    *)
(*    del, Esum_del  : deleting one index from a sum                   *)
(*    Esum_prod      : a product of sums is a double sum               *)
(*    Esum_swap      : the two orders of summation agree               *)
(*    cg             : congruence mod p, transported into Z            *)
(*    psi s u        : the substitution (1 - s u)/(1 - s)              *)
(*    cg_psi         : (1-s) psi(s,u) = 1 - s u   mod p                *)
(*    K u            : the inner sum, evaluated                        *)
(*    norm_Jsum      : N(J(chi,chi)) = p                               *)
(*                                                                    *)
(*  THE POINT OF THIS FILE IS THAT IT NEVER LEAVES Z[om].  The         *)
(*  textbook route to |J|^2 = p goes through the Gauss sum, via        *)
(*  g(chi)^3 = p J and |g|^2 = p, and Gauss sums live in Z[om, zeta_p] *)
(*  -- a cyclotomic extension this development does not have and which *)
(*  would be a large project of its own.  The double-sum proof below   *)
(*  needs only F_p and Z[om], both of which are already here.          *)
(*                                                                    *)
(*  THE ARGUMENT, in one line each:                                    *)
(*    J . conj J = sum_{t,s} chi(t) chi(1-t) conj chi(s) conj chi(1-s) *)
(*    put t = s u :  chi(su) conj chi(s) = chi(u), so the inner sum    *)
(*      becomes sum_u chi(u) chi((1-su)/(1-s))                         *)
(*    swap, and for fixed u the map s |-> (1-su)/(1-s) is a bijection  *)
(*      F_p \ {1} -> F_p \ {u}, so the inner sum is -1 - chi(u)        *)
(*    at u = 1 it is instead p - 2, and orthogonality kills the rest:  *)
(*      (p-2) + 1 + 1 = p.                                             *)
(*                                                                    *)
(*  TWO BIJECTIONS DO ALL THE WORK and they are of different kinds.    *)
(*  t |-> s t is multiplication, and permutes ALL of F_p including 0,  *)
(*  which is why mulmod_bij is proved over seq 0 p rather than reusing *)
(*  units_perm.  s |-> (1-su)/(1-s) is not multiplication by anything, *)
(*  and its target F_p \ {u} MOVES WITH u -- hence del, and hence      *)
(*  Esum_bij2 rather than a permutation lemma.                         *)
(*                                                                    *)
(*  ALL THE MODULAR ALGEBRA IS PUSHED INTO Z.  cg a z says             *)
(*  p | a - z with a a natural and z an integer, so nat subtraction    *)
(*  and its truncation never appear in a hypothesis being manipulated; *)
(*  every identity becomes a linear combination of divisibility        *)
(*  witnesses that ring and lia can check.  cg_psi is the one real     *)
(*  computation, and its statement -- (1-s) V = 1 - s u -- is the      *)
(*  characterisation of psi that both the range and the injectivity    *)
(*  arguments then read off, by substituting u and by cross-           *)
(*  multiplying respectively.                                          *)
(*                                                                    *)
(*  WHY u = 1 IS SPECIAL: there psi is constantly 1, so the bijection  *)
(*  degenerates to a constant map and the inner sum counts the index   *)
(*  set instead of vanishing.  That single term is where the p comes   *)
(*  from; everything else contributes the +2.                          *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot FpField
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat
        CEisensteinCubicMul CEisensteinCubicSupp CEisensteinCubicFun
        CEisensteinSum CEisensteinJacobi.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  deleting one element from a list                               *)
(* ----------------------------------------------------------------- *)
Definition del (a : nat) (l : list nat) : list nat :=
  filter (fun x => negb (x =? a)%nat) l.

Lemma In_del : forall a l x, In x (del a l) <-> In x l /\ x <> a.
Proof.
  intros a l x. unfold del. rewrite filter_In. split.
  - intros [H1 H2]. split; [ exact H1 | ].
    intro Hc. subst x. rewrite Nat.eqb_refl in H2. discriminate.
  - intros [H1 H2]. split; [ exact H1 | ].
    apply negb_true_iff, Nat.eqb_neq. exact H2.
Qed.

Lemma NoDup_del : forall a l, NoDup l -> NoDup (del a l).
Proof. intros a l H. apply NoDup_filter. exact H. Qed.

Lemma del_perm : forall a l, NoDup l -> In a l -> Permutation l (a :: del a l).
Proof.
  intros a l Hnd Hin. apply NoDup_Permutation.
  - exact Hnd.
  - constructor; [ | apply NoDup_del; exact Hnd ].
    intro Hc. apply (proj1 (In_del a l a) Hc). reflexivity.
  - intro x. split.
    + intro Hx. destruct (Nat.eq_dec x a) as [-> | Hne];
        [ left; reflexivity | right; apply In_del; split; assumption ].
    + intros [Hx | Hx]; [ subst x; exact Hin | apply (proj1 (In_del a l x) Hx) ].
Qed.

Lemma Esum_del : forall f a l, NoDup l -> In a l ->
  Esum f l = eadd (f a) (Esum f (del a l)).
Proof.
  intros f a l Hnd Hin.
  rewrite (Esum_perm f l (a :: del a l) (del_perm a l Hnd Hin)).
  apply Esum_cons.
Qed.

Lemma length_del : forall a l, NoDup l -> In a l ->
  (length l = S (length (del a l)))%nat.
Proof.
  intros a l Hnd Hin.
  rewrite (Permutation_length (del_perm a l Hnd Hin)). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  double sums                                                    *)
(* ----------------------------------------------------------------- *)
Lemma Esum_zero_ext : forall f l, (forall x, In x l -> f x = ezero) -> Esum f l = ezero.
Proof.
  intros f l H. induction l as [| a l IH]; [ reflexivity | ].
  rewrite Esum_cons, (H a (or_introl eq_refl)), IH;
    [ ring | intros x Hx; apply H; right; exact Hx ].
Qed.

Lemma Esum_scale_r : forall c f l,
  Esum (fun x => emul (f x) c) l = emul (Esum f l) c.
Proof.
  intros c f l. induction l as [| x l IH]; [ cbn; unfold Esum; cbn; ring | ].
  rewrite !Esum_cons, IH. ring.
Qed.

Lemma Esum_add : forall f g l,
  Esum (fun x => eadd (f x) (g x)) l = eadd (Esum f l) (Esum g l).
Proof.
  intros f g l. induction l as [| x l IH]; [ cbn; unfold Esum; cbn; ring | ].
  rewrite !Esum_cons, IH. ring.
Qed.

Lemma Esum_prod : forall f g l1 l2,
  emul (Esum f l1) (Esum g l2)
  = Esum (fun x => Esum (fun y => emul (f x) (g y)) l2) l1.
Proof.
  intros f g l1 l2. induction l1 as [| x l1 IH]; [ cbn; unfold Esum; cbn; ring | ].
  rewrite !Esum_cons, <- IH, Esum_scale_l. ring.
Qed.

Lemma Esum_swap : forall (F : nat -> nat -> Eis) l1 l2,
  Esum (fun x => Esum (fun y => F x y) l2) l1
  = Esum (fun y => Esum (fun x => F x y) l1) l2.
Proof.
  intros F l1 l2. revert F. induction l1 as [| x l1 IH]; intro F.
  - rewrite Esum_nil. symmetry. apply Esum_zero_ext. intros y _. apply Esum_nil.
  - rewrite Esum_cons, IH.
    rewrite <- Esum_add. apply Esum_ext. intros y _.
    rewrite Esum_cons. reflexivity.
Qed.


Lemma del_notin : forall a l, ~ In a l -> del a l = l.
Proof.
  intros a l. unfold del. induction l as [| x l IH]; intro H; [ reflexivity | ].
  cbn [filter]. destruct (x =? a)%nat eqn:E; cbn [negb].
  - exfalso. apply Nat.eqb_eq in E. subst x. apply H. left. reflexivity.
  - f_equal. apply IH. intro Hc. apply H. right. exact Hc.
Qed.

Lemma econj_mul : forall x y, econj (emul x y) = emul (econj x) (econj y).
Proof.
  intros [a b] [c d]. unfold econj, emul; cbn [ea eb]. apply Eis_eq; ring.
Qed.

Lemma eZ_add : forall m n, eadd (eZ m) (eZ n) = eZ (m + n).
Proof. intros m n. unfold eZ, eadd; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma eone_eZ : eone = eZ 1.
Proof. reflexivity. Qed.

Lemma eZ_inj : forall m n, eZ m = eZ n -> m = n.
Proof. intros m n H. change (ea (eZ m) = ea (eZ n)). rewrite H. reflexivity. Qed.

Lemma Esum_const_one : forall l, Esum (fun _ => eone) l = eZ (Z.of_nat (length l)).
Proof.
  intro l. induction l as [| x l IH]; [ reflexivity | ].
  rewrite Esum_cons, IH, eone_eZ, eZ_add. cbn [length]. f_equal. lia.
Qed.

Lemma cuberoot_sq : forall z, cuberoot z -> emul z z = econj z.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

(* ================================================================= *)
(*  C.  the norm of the Jacobi sum                                     *)
(* ================================================================= *)
Section NormJ.

Variable p : nat.
Variable pi : Eis.
Variable t0 : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t0) eom).

Notation ch := (chn p pi).
Notation P := (Z.of_nat p).

(* ---- congruence mod p, transported to Z ------------------------- *)
Definition cg (a : nat) (z : Z) : Prop := (P | Z.of_nat a - z).

Lemma cg_refl : forall a, cg a (Z.of_nat a).
Proof. intro a. exists 0. ring. Qed.

Lemma cg_mod : forall a, cg (a mod p) (Z.of_nat a).
Proof.
  intro a. exists (- Z.of_nat (a / p)).
  assert (E : (a = p * (a / p) + a mod p)%nat) by apply Nat.div_mod_eq. lia.
Qed.

Lemma cg_step : forall a z z', cg a z -> (P | z - z') -> cg a z'.
Proof.
  intros a z z' [c Hc] [d Hd]. exists (c + d). lia.
Qed.

Lemma cg_mul : forall a b z w, cg a z -> cg b w -> cg (a * b) (z * w).
Proof.
  intros a b z w [c Hc] [d Hd].
  exists (c * Z.of_nat b + d * z). rewrite Nat2Z.inj_mul. nia.
Qed.

Lemma cg_eq : forall a b, (a < p)%nat -> (b < p)%nat ->
  (P | Z.of_nat a - Z.of_nat b) -> a = b.
Proof.
  intros a b Ha Hb [c Hc].
  assert (Hb2 : - P < Z.of_nat a - Z.of_nat b < P) by lia.
  destruct (Z.lt_trichotomy c 0) as [H | [H | H]].
  - assert (c * P <= (-1) * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - rewrite H in Hc. lia.
  - assert (1 * P <= c * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma cg_chn : forall a b, (P | Z.of_nat a - Z.of_nat b) -> ch a = ch b.
Proof.
  intros a b H. unfold chn.
  apply (chiv_cong_eq p pi t0 Hp Hp7 Hdiv Hn Ht).
  apply (econg_eZ_of_dvd p pi Hp Hn). exact H.
Qed.

Lemma cg_inv : forall b, (1 <= b <= p - 1)%nat -> cg (b * finv p b) 1.
Proof.
  intros b Hb. apply (cg_step _ (Z.of_nat ((b * finv p b) mod p))).
  - apply (cg_step _ (Z.of_nat (b * finv p b))); [ apply cg_refl | ].
    destruct (cg_mod (b * finv p b)%nat) as [c Hc]. exists (- c). lia.
  - rewrite (inv_correct p b Hp Hb). exists 0. ring.
Qed.

(* ---- the field operations we need -------------------------------- *)
Definition fm (a b : nat) : nat := (a * b) mod p.
Definition sb (x : nat) : nat := (1 + p - x) mod p.

Lemma fm_lt : forall a b, (fm a b < p)%nat.
Proof. intros a b. unfold fm. apply Nat.mod_upper_bound. lia. Qed.

Lemma sb_lt : forall x, (sb x < p)%nat.
Proof. intro x. unfold sb. apply Nat.mod_upper_bound. lia. Qed.

Lemma cg_fm : forall a b, cg (fm a b) (Z.of_nat a * Z.of_nat b).
Proof.
  intros a b. unfold fm.
  apply (cg_step _ (Z.of_nat (a * b))); [ apply cg_mod | ].
  rewrite Nat2Z.inj_mul. exists 0. ring.
Qed.

Lemma cg_sb : forall x, (x <= p)%nat -> cg (sb x) (1 - Z.of_nat x).
Proof.
  intro x. intro Hx. unfold sb.
  apply (cg_step _ (Z.of_nat (1 + p - x))); [ apply cg_mod | ].
  exists 1. lia.
Qed.

Lemma sb_range : forall s, (2 <= s <= p - 1)%nat -> (1 <= sb s <= p - 1)%nat.
Proof.
  intros s Hs. unfold sb.
  rewrite (Nat.mod_small (1 + p - s) p) by lia. lia.
Qed.

Lemma sb_0 : sb 0 = 1%nat.
Proof.
  unfold sb. rewrite Nat.sub_0_r.
  replace (1 + p)%nat with (1 + 1 * p)%nat by lia.
  rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia.
Qed.

Lemma sb_1 : sb 1 = 0%nat.
Proof.
  unfold sb. replace (1 + p - 1)%nat with p by lia. apply Nat.Div0.mod_same.
Qed.

Lemma chn_zero : ch 0 = ezero.
Proof.
  unfold chn. apply (chiv_zero p pi Hp Hn). exists ezero.
  replace (Z.of_nat 0) with 0 by reflexivity. unfold eZ, ezero, emul; cbn [ea eb].
  apply Eis_eq; ring.
Qed.

(* ---- the two summands ------------------------------------------- *)
Definition fJ (t : nat) : Eis := emul (ch t) (ch (sb t)).
Definition gJ (s : nat) : Eis := emul (econj (ch s)) (econj (ch (sb s))).

Lemma seq0p : seq 0 p = 0%nat :: 1%nat :: seq 2 (p - 2).
Proof.
  replace p with (S (S (p - 2))) at 1 by lia. cbn [seq].
  repeat f_equal; lia.
Qed.

Lemma JsumF : Esum fJ (seq 0 p) = Jsum p pi.
Proof.
  rewrite seq0p, !Esum_cons.
  assert (H0 : fJ 0 = ezero) by (unfold fJ; rewrite chn_zero; ring).
  assert (H1 : fJ 1 = ezero) by (unfold fJ; rewrite sb_1, chn_zero; ring).
  rewrite H0, H1.
  unfold Jsum.
  rewrite (Esum_ext fJ (fun t => emul (ch t) (ch (1 + p - t)%nat)) (seq 2 (p - 2))).
  - ring.
  - intros x Hx. apply in_seq in Hx. unfold fJ, sb.
    rewrite (Nat.mod_small (1 + p - x) p) by lia. reflexivity.
Qed.

Lemma gJ_conj : forall s, gJ s = econj (fJ s).
Proof. intro s. unfold gJ, fJ. rewrite econj_mul. reflexivity. Qed.

(* ---- reindexing t = s.u ------------------------------------------ *)
Lemma mulmod_bij : forall s, (2 <= s <= p - 1)%nat -> forall (F : nat -> Eis),
  Esum F (seq 0 p) = Esum (fun u => F (fm s u)) (seq 0 p).
Proof.
  intros s Hs F. symmetry.
  apply (Esum_bij2 F (seq 0 p) (seq 0 p) (fm s)).
  - apply seq_NoDup.
  - lia.
  - intros x _. apply in_seq. pose proof (fm_lt s x). lia.
  - intros x y Hx Hy He. apply in_seq in Hx. apply in_seq in Hy.
    (* p | s(x - y) and p does not divide s *)
    assert (Hd : (P | Z.of_nat s * (Z.of_nat x - Z.of_nat y))).
    { destruct (cg_fm s x) as [c Hc]. destruct (cg_fm s y) as [d Hd].
      rewrite He in Hc. exists (d - c). nia. }
    assert (Hns : ~ (P | Z.of_nat s)).
    { intros [c Hc].
      assert (Hb : 0 < Z.of_nat s < P) by lia.
      destruct (Z.le_gt_cases c 0) as [H | H].
      - assert (c * P <= 0 * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
      - assert (1 * P <= c * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    destruct (prime_mult P Hp _ _ Hd) as [H | H]; [ contradiction | ].
    apply cg_eq; [ lia | lia | exact H ].
Qed.

(* ---- the term identity ------------------------------------------- *)
Definition psi (s u : nat) : nat := fm (sb (fm s u)) (finv p (sb s)).

Lemma term_id : forall s u, (2 <= s <= p - 1)%nat -> (u < p)%nat ->
  emul (fJ (fm s u)) (gJ s) = emul (ch u) (ch (psi s u)).
Proof.
  intros s u Hs Hu.
  assert (Hsr : (1 <= s <= p - 1)%nat) by lia.
  assert (Hsb : (1 <= sb s <= p - 1)%nat) by (apply sb_range; exact Hs).
  unfold fJ, gJ.
  rewrite (chn_conj p pi t0 Hp Hp7 Hdiv Hn Ht s Hsr).
  rewrite (chn_conj p pi t0 Hp Hp7 Hdiv Hn Ht (sb s) Hsb).
  (* first pair collapses to ch u *)
  assert (E1 : emul (ch (fm s u)) (ch (finv p s)) = ch u).
  { rewrite <- (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht).
    change ((fm s u * finv p s) mod p)%nat with (fm (fm s u) (finv p s)).
    apply cg_chn.
    (* (s u) (s^{-1}) = u  mod p *)
    destruct (cg_fm (fm s u) (finv p s)) as [c Hc].
    destruct (cg_fm s u) as [d Hd].
    destruct (cg_inv s Hsr) as [e He].
    rewrite Nat2Z.inj_mul in He.
    exists (c + Z.of_nat (finv p s) * d + Z.of_nat u * e).
    assert (Q1 : Z.of_nat (fm (fm s u) (finv p s))
                 = Z.of_nat (fm s u) * Z.of_nat (finv p s) + c * P) by lia.
    assert (Q2 : Z.of_nat (fm s u) = Z.of_nat s * Z.of_nat u + d * P) by lia.
    assert (Q3 : Z.of_nat s * Z.of_nat (finv p s) = 1 + e * P) by lia.
    rewrite Q1, Q2.
    replace ((Z.of_nat s * Z.of_nat u + d * P) * Z.of_nat (finv p s) + c * P
             - Z.of_nat u)
      with ((Z.of_nat s * Z.of_nat (finv p s)) * Z.of_nat u
            + d * Z.of_nat (finv p s) * P + c * P - Z.of_nat u) by ring.
    rewrite Q3. ring. }
  (* second pair is the definition of psi *)
  assert (E2 : emul (ch (sb (fm s u))) (ch (finv p (sb s))) = ch (psi s u)).
  { unfold psi, fm. rewrite (chn_mul p pi t0 Hp Hp7 Hdiv Hn Ht). reflexivity. }
  rewrite <- E1, <- E2. ring.
Qed.

(* ---- psi is a bijection  F_p \ {1}  ->  F_p \ {u} ---------------- *)
Lemma sb_unit : forall s, (s < p)%nat -> s <> 1%nat -> (1 <= sb s <= p - 1)%nat.
Proof.
  intros s Hs H1. destruct (Nat.eq_dec s 0) as [-> | Hs0].
  - rewrite sb_0. lia.
  - unfold sb. rewrite (Nat.mod_small (1 + p - s) p) by lia. lia.
Qed.

Lemma cg_psi : forall s u, (s < p)%nat -> s <> 1%nat -> (u < p)%nat ->
  (P | (1 - Z.of_nat s) * Z.of_nat (psi s u) - (1 - Z.of_nat s * Z.of_nat u)).
Proof.
  intros s u Hs H1 Hu.
  assert (Hsb : (1 <= sb s <= p - 1)%nat) by (apply sb_unit; assumption).
  destruct (cg_fm (sb (fm s u)) (finv p (sb s))) as [a Ha].
  change (fm (sb (fm s u)) (finv p (sb s))) with (psi s u) in Ha.
  destruct (cg_inv (sb s) Hsb) as [b Hb]. rewrite Nat2Z.inj_mul in Hb.
  destruct (cg_sb (fm s u) ltac:(pose proof (fm_lt s u); lia)) as [c Hc].
  destruct (cg_fm s u) as [d Hd].
  destruct (cg_sb s ltac:(lia)) as [e He].
  set (V := Z.of_nat (psi s u)) in *.
  set (B := Z.of_nat (sb s)) in *.
  set (I := Z.of_nat (finv p (sb s))) in *.
  set (W := Z.of_nat (sb (fm s u))) in *.
  set (M := Z.of_nat (fm s u)) in *.
  (* Ha : V - W * I = a P ;  Hb : B * I - 1 = b P ;  Hc : W - (1 - M) = c P
     Hd : M - s u = d P    ;  He : B - (1 - s) = e P *)
  exists (B * a + W * b + c - d - e * V).
  assert (Q1 : V = W * I + a * P) by lia.
  assert (Q2 : B * I = 1 + b * P) by lia.
  assert (Q3 : W = 1 - M + c * P) by lia.
  assert (Q4 : M = Z.of_nat s * Z.of_nat u + d * P) by lia.
  assert (Q5 : B = 1 - Z.of_nat s + e * P) by lia.
  (* B V = W (B I) + B a P = W + W b P + B a P *)
  assert (R1 : B * V = W + W * b * P + B * a * P).
  { rewrite Q1.
    replace (B * (W * I + a * P)) with (W * (B * I) + B * a * P) by ring.
    rewrite Q2. ring. }
  assert (R2 : W = 1 - Z.of_nat s * Z.of_nat u - d * P + c * P)
    by (rewrite Q3, Q4; ring).
  replace ((1 - Z.of_nat s) * V) with (B * V - e * P * V) by (rewrite Q5; ring).
  rewrite R1, R2. ring.
Qed.

Lemma P_ndvd_small : forall z, 0 < z < P -> ~ (P | z).
Proof.
  intros z Hz [c Hc].
  destruct (Z.le_gt_cases c 0) as [H | H].
  - assert (c * P <= 0 * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - assert (1 * P <= c * P) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma psi_ne_u : forall s u, (s < p)%nat -> s <> 1%nat -> (2 <= u <= p - 1)%nat ->
  psi s u <> u.
Proof.
  intros s u Hs H1 Hu Hc.
  destruct (cg_psi s u Hs H1 ltac:(lia)) as [k Hk]. rewrite Hc in Hk.
  (* (1-s) u - (1 - s u) = u - 1 *)
  apply (P_ndvd_small (Z.of_nat u - 1)); [ lia | ].
  exists k. lia.
Qed.

Lemma psi_inj : forall s s' u, (s < p)%nat -> s <> 1%nat -> (s' < p)%nat -> s' <> 1%nat ->
  (2 <= u <= p - 1)%nat -> psi s u = psi s' u -> s = s'.
Proof.
  intros s s' u Hs H1 Hs' H1' Hu He.
  destruct (cg_psi s u Hs H1 ltac:(lia)) as [k Hk].
  destruct (cg_psi s' u Hs' H1' ltac:(lia)) as [m Hm].
  rewrite <- He in Hm.
  set (V := Z.of_nat (psi s u)) in *.
  set (S1 := Z.of_nat s) in *. set (S2 := Z.of_nat s') in *.
  set (U := Z.of_nat u) in *.
  (* cross-multiplying kills V *)
  assert (Hcross : (P | (S1 - S2) * (1 - U))).
  { exists ((1 - S1) * m - (1 - S2) * k).
    assert (Q1 : (1 - S1) * V = 1 - S1 * U + k * P) by lia.
    assert (Q2 : (1 - S2) * V = 1 - S2 * U + m * P) by lia.
    assert (Q3 : (1 - S2) * ((1 - S1) * V) = (1 - S1) * ((1 - S2) * V)) by ring.
    rewrite Q1, Q2 in Q3.
    assert (E : (S1 - S2) * (1 - U) - ((1 - S1) * m - (1 - S2) * k) * P
                = (1 - S2) * (1 - S1 * U + k * P)
                  - (1 - S1) * (1 - S2 * U + m * P)) by ring.
    rewrite Q3 in E. lia. }
  assert (Hu1 : ~ (P | 1 - U)).
  { intro Hd. apply (P_ndvd_small (U - 1)); [ lia | ].
    destruct Hd as [c Hc]. exists (- c). lia. }
  destruct (prime_mult P Hp _ _ Hcross) as [H | H]; [ | contradiction ].
  apply cg_eq; [ lia | lia | exact H ].
Qed.

Lemma psi_0 : forall u, psi 0 u = 1%nat.
Proof.
  intro u. unfold psi, fm.
  rewrite Nat.mul_0_l, Nat.Div0.mod_0_l, sb_0, (finv_1 p ltac:(lia)).
  rewrite Nat.mul_1_r. apply Nat.mod_small. lia.
Qed.

Lemma psi_one : forall s, (2 <= s <= p - 1)%nat -> psi s 1 = 1%nat.
Proof.
  intros s Hs.
  assert (Hsb : (1 <= sb s <= p - 1)%nat) by (apply sb_range; exact Hs).
  unfold psi. replace (fm s 1) with s.
  - unfold fm. apply (inv_correct p (sb s) Hp Hsb).
  - unfold fm. rewrite Nat.mul_1_r, Nat.mod_small by lia. reflexivity.
Qed.

(* ---- the inner sum K u ------------------------------------------- *)
Definition K (u : nat) : Eis := Esum (fun s => ch (psi s u)) (seq 2 (p - 2)).

Lemma D_nodup : NoDup (0%nat :: seq 2 (p - 2)).
Proof.
  constructor; [ | apply seq_NoDup ].
  intro Hc. apply in_seq in Hc. lia.
Qed.

Lemma K_one : K 1 = eZ (Z.of_nat (p - 2)).
Proof.
  unfold K.
  rewrite (Esum_ext _ (fun _ => eone) (seq 2 (p - 2))).
  - rewrite Esum_const_one, length_seq. reflexivity.
  - intros x Hx. apply in_seq in Hx.
    rewrite (psi_one x ltac:(lia)). exact (chn_one p pi t0 Hp Hp7 Hdiv Hn Ht).
Qed.

Lemma K_gen : forall u, (2 <= u <= p - 1)%nat -> K u = esub (eopp (ch u)) eone.
Proof.
  intros u Hu.
  (* the sum over F_p \ {1}, which adds the s = 0 term *)
  assert (Hbij : Esum (fun s => ch (psi s u)) (0%nat :: seq 2 (p - 2))
                 = Esum ch (del u (seq 0 p))).
  { apply (Esum_bij2 ch (0%nat :: seq 2 (p - 2)) (del u (seq 0 p)) (fun s => psi s u)).
    - exact D_nodup.
    - pose proof (length_del u (seq 0 p) (seq_NoDup _ _)
                    ltac:(apply in_seq; lia)) as HL.
      rewrite length_seq in HL.
      cbn [length]. rewrite length_seq. lia.
    - intros x Hx. apply In_del. split.
      + apply in_seq. pose proof (fm_lt (sb (fm x u)) (finv p (sb (fm x u)))).
        unfold psi. pose proof (fm_lt (sb (fm x u)) (finv p (sb x))). lia.
      + destruct Hx as [Hx | Hx].
        * subst x. rewrite psi_0. lia.
        * apply in_seq in Hx. apply psi_ne_u; [ lia | lia | lia ].
    - intros x y Hx Hy He.
      assert (Hx' : (x < p)%nat /\ x <> 1%nat).
      { destruct Hx as [Hx | Hx]; [ subst x; lia | apply in_seq in Hx; lia ]. }
      assert (Hy' : (y < p)%nat /\ y <> 1%nat).
      { destruct Hy as [Hy | Hy]; [ subst y; lia | apply in_seq in Hy; lia ]. }
      apply (psi_inj x y u); try lia; try tauto. }
  rewrite Esum_cons, psi_0, (chn_one p pi t0 Hp Hp7 Hdiv Hn Ht) in Hbij.
  (* the full character sum is zero *)
  pose proof (char_sum_zero_full p pi t0 Hp Hp7 Hdiv Hn Ht) as Hzero.
  change (Esum (fun n => chiv p pi (eZ (Z.of_nat n))) (seq 0 p))
    with (Esum ch (seq 0 p)) in Hzero.
  rewrite (Esum_del ch u (seq 0 p) (seq_NoDup _ _) ltac:(apply in_seq; lia)) in Hzero.
  (* eone + K u = - ch u *)
  unfold K. rewrite <- Hbij in Hzero. unfold esub.
  assert (E : Esum (fun s => ch (psi s u)) (seq 2 (p - 2))
              = eadd (eadd (ch u) (eadd eone (Esum (fun s => ch (psi s u))
                                                   (seq 2 (p - 2)))))
                     (eadd (eopp (ch u)) (eopp eone))) by ring.
  rewrite E, Hzero. ring.
Qed.

(* ---- assembling ------------------------------------------------- *)
Lemma Esum_opp : forall f l, Esum (fun x => eopp (f x)) l = eopp (Esum f l).
Proof.
  intros f l. induction l as [| x l IH]; [ cbn; unfold Esum; cbn; ring | ].
  rewrite !Esum_cons, IH. ring.
Qed.

Lemma seq1p : seq 1 (p - 1) = 1%nat :: seq 2 (p - 2).
Proof.
  replace (p - 1)%nat with (S (p - 2)) at 1 by lia. cbn [seq].
  repeat f_equal; lia.
Qed.

Lemma sum_ch_tail : Esum ch (seq 2 (p - 2)) = eopp eone.
Proof.
  pose proof (char_sum_zero p pi t0 Hp Hp7 Hdiv Hn Ht) as H.
  change (Esum (fun n => chiv p pi (eZ (Z.of_nat n))) (seq 1 (p - 1)))
    with (Esum ch (seq 1 (p - 1))) in H.
  rewrite seq1p, Esum_cons in H. cbv beta in H.
  rewrite (chn_one p pi t0 Hp Hp7 Hdiv Hn Ht) in H.
  assert (E : Esum ch (seq 2 (p - 2))
              = esub (eadd eone (Esum ch (seq 2 (p - 2)))) eone) by ring.
  rewrite E, H. unfold esub. ring.
Qed.

Lemma sum_chsq_tail : Esum (fun u => econj (ch u)) (seq 2 (p - 2)) = eopp eone.
Proof.
  pose proof (chisq_sum_zero p pi t0 Hp Hp7 Hdiv Hn Ht) as H.
  rewrite seq1p, Esum_cons in H. cbv beta in H.
  rewrite (chn_one p pi t0 Hp Hp7 Hdiv Hn Ht) in H.
  assert (Hc : econj eone = eone) by reflexivity.
  rewrite Hc in H.
  assert (E : Esum (fun u => econj (ch u)) (seq 2 (p - 2))
              = esub (eadd eone (Esum (fun u => econj (ch u)) (seq 2 (p - 2)))) eone)
    by ring.
  rewrite E, H. unfold esub. ring.
Qed.

Lemma Esum_split01 : forall F,
  Esum F (seq 0 p) = eadd (F 0%nat) (eadd (F 1%nat) (Esum F (seq 2 (p - 2)))).
Proof. intro F. rewrite seq0p, !Esum_cons. reflexivity. Qed.

Lemma gJ_0 : gJ 0 = ezero.
Proof. unfold gJ. rewrite chn_zero, econj_zero. ring. Qed.

Lemma gJ_1 : gJ 1 = ezero.
Proof. unfold gJ. rewrite sb_1, chn_zero, econj_zero. ring. Qed.

Theorem norm_Jsum : enorm (Jsum p pi) = Z.of_nat p.
Proof.
  (* the conjugate sum *)
  assert (HB : Esum gJ (seq 0 p) = econj (Esum fJ (seq 0 p))).
  { rewrite econj_Esum. apply Esum_ext. intros x _. apply gJ_conj. }
  (* expand the product, swap, and drop the two degenerate outer terms *)
  assert (Hstep1 : emul (Esum fJ (seq 0 p)) (Esum gJ (seq 0 p))
                   = Esum (fun s => Esum (fun t => emul (fJ t) (gJ s)) (seq 0 p))
                          (seq 2 (p - 2))).
  { rewrite Esum_prod, Esum_swap.
    rewrite (Esum_split01 (fun s => Esum (fun t => emul (fJ t) (gJ s)) (seq 0 p))).
    cbv beta.
    assert (Z0 : Esum (fun t => emul (fJ t) (gJ 0)) (seq 0 p) = ezero)
      by (apply Esum_zero_ext; intros x _; rewrite gJ_0; ring).
    assert (Z1 : Esum (fun t => emul (fJ t) (gJ 1)) (seq 0 p) = ezero)
      by (apply Esum_zero_ext; intros x _; rewrite gJ_1; ring).
    rewrite Z0, Z1. ring. }
  (* reindex t = s.u and use the term identity *)
  assert (Hstep2 : Esum (fun s => Esum (fun t => emul (fJ t) (gJ s)) (seq 0 p))
                        (seq 2 (p - 2))
                   = Esum (fun u => emul (ch u) (K u)) (seq 0 p)).
  { rewrite (Esum_ext _ (fun s => Esum (fun u => emul (ch u) (ch (psi s u)))
                                       (seq 0 p)) (seq 2 (p - 2))).
    - rewrite Esum_swap. apply Esum_ext. intros u _.
      unfold K. rewrite Esum_scale_l. reflexivity.
    - intros s Hs. apply in_seq in Hs.
      rewrite (mulmod_bij s ltac:(lia) (fun t => emul (fJ t) (gJ s))).
      apply Esum_ext. intros u Hu. apply in_seq in Hu.
      apply term_id; lia. }
  (* evaluate term by term *)
  assert (Hstep3 : Esum (fun u => emul (ch u) (K u)) (seq 0 p)
                   = eZ (Z.of_nat p)).
  { rewrite (Esum_split01 (fun u => emul (ch u) (K u))). cbv beta.
    rewrite chn_zero, (chn_one p pi t0 Hp Hp7 Hdiv Hn Ht), K_one.
    rewrite (Esum_ext _ (fun u => eopp (eadd (econj (ch u)) (ch u)))
                      (seq 2 (p - 2))).
    - rewrite Esum_opp, Esum_add, sum_ch_tail, sum_chsq_tail.
      assert (E : eadd (emul ezero (K 0%nat))
                       (eadd (emul eone (eZ (Z.of_nat (p - 2))))
                             (eopp (eadd (eopp eone) (eopp eone))))
                  = eadd (eZ (Z.of_nat (p - 2))) (eadd eone eone)) by ring.
      rewrite E, eone_eZ, !eZ_add. f_equal. lia.
    - intros u Hu. apply in_seq in Hu.
      rewrite (K_gen u ltac:(lia)).
      assert (Hcr : cuberoot (ch u))
        by (apply (chn_cuberoot p pi Hp Hp7 Hn); lia).
      rewrite <- (cuberoot_sq (ch u) Hcr). unfold esub. ring. }
  (* and read off the norm *)
  rewrite HB, JsumF in Hstep1.
  rewrite Hstep2, Hstep3 in Hstep1.
  apply eZ_inj. rewrite <- Hstep1. symmetry. exact (emul_econj (Jsum p pi)).
Qed.

End NormJ.

Print Assumptions Esum_swap.
Print Assumptions cg_psi.
Print Assumptions K_gen.
Print Assumptions norm_Jsum.
