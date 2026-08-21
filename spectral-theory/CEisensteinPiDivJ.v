(* ================================================================= *)
(*  CEisensteinPiDivJ.v  —  pi divides J, so J IS the primary prime.   *)
(*                                                                    *)
(*    Zsum                : integer-valued sums over an index list     *)
(*    eZ_Zsum, econg_Esum : the bridges to Z[om]-valued sums           *)
(*    mulmod_perm0        : x |-> g x permutes ALL of F_p, 0 included  *)
(*    power_sum           : sum_t t^a = 0 mod p   for a < p-1          *)
(*    poly_sum            : sum_t t^a (1-t)^b = 0  for a + b < p-1     *)
(*    ch_pow              : chi(t) = t^{(p-1)/3} mod pi, at t = 0 too  *)
(*    pi_dvd_Jsum         : pi | J                                     *)
(*    jacobi_eq_primary   : J IS the primary associate of pi           *)
(*                                                                    *)
(*  THIS CLOSES THE CLASSICAL THEOREM.  N(J) = p came from brick 4 and *)
(*  J = -1 mod 3 from brick 5, which together placed J among the       *)
(*  associates of pi or of conj pi without saying which.  pi | J is    *)
(*  what decides it, and with it J is pinned exactly: the Jacobi sum   *)
(*  of the cubic character mod pi is the primary associate of pi.      *)
(*                                                                    *)
(*  THE BINOMIAL THEOREM IS NEVER STATED, and not needing it is the    *)
(*  point of poly_sum.  The textbook argument expands (1-t)^k by       *)
(*  binomial coefficients and checks that no exponent k + j reaches    *)
(*  p - 1.  Here the expansion is replaced by an induction on b:       *)
(*                                                                    *)
(*      t^a (1-t)^(b+1)  =  t^a (1-t)^b  -  t^(a+1) (1-t)^b            *)
(*                                                                    *)
(*  so the sum splits in two and the induction hypothesis covers both, *)
(*  because the total degree a + b rises by exactly one each time.     *)
(*  No binomial coefficient function is defined and none is needed.    *)
(*                                                                    *)
(*  THE DEGREE BOUND IS THE WHOLE CONTENT.  power_sum vanishes for     *)
(*  every exponent below p - 1 and fails at p - 1, where the sum is    *)
(*  -1 rather than 0.  For the Jacobi sum a = b = k = (p-1)/3, so the  *)
(*  total degree is 2k while the dangerous exponent is 3k: the         *)
(*  argument has exactly one third of the range to spare, and that     *)
(*  slack is the reason the cubic case works at all.                   *)
(*                                                                    *)
(*  THE PERMUTATION MUST COVER 0.  units_perm reindexes seq 1 (p-1),   *)
(*  which is enough for character sums but not for power sums -- those *)
(*  run over the whole field.  mulmod_perm0 does seq 0 p, and it is    *)
(*  cancel_mod rather than mulmod_inj that makes the 0 case go         *)
(*  through, since mulmod_inj assumes its arguments are units.         *)
(*                                                                    *)
(*  chi(t) = t^k HOLDS AT t = 0 as well, both sides being zero -- the  *)
(*  chi(0) = 0 convention from brick 1 paying off again.  That is what *)
(*  lets every sum here run over seq 0 p with no exceptional term.     *)
(*                                                                    *)
(*  Zsum is a separate integer-valued layer rather than a reuse of     *)
(*  Esum: the statements here are divisibility in Z, which is what     *)
(*  lia can discharge, and pushing them through Z[om] would gain       *)
(*  nothing.  eZ_Zsum and econg_Esum are the only bridges needed.      *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot FpField
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat
        CEisensteinCubicMul CEisensteinCubicSupp CEisensteinCubicFun
        CEisensteinPrimary CEisensteinSum CEisensteinJacobi CEisensteinNormJ
        CEisensteinJPrimary.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  integer-valued sums over a list of indices                     *)
(* ----------------------------------------------------------------- *)
Definition Zsum (f : nat -> Z) (l : list nat) : Z := fold_right Z.add 0 (map f l).

Lemma Zsum_nil : forall f, Zsum f [] = 0.
Proof. reflexivity. Qed.

Lemma Zsum_cons : forall f x l, Zsum f (x :: l) = f x + Zsum f l.
Proof. reflexivity. Qed.

Lemma Zsum_ext : forall f h l,
  (forall x, In x l -> f x = h x) -> Zsum f l = Zsum h l.
Proof.
  intros f h l. induction l as [| x l IH]; intro He; [ reflexivity | ].
  rewrite !Zsum_cons, (He x (or_introl eq_refl)), IH;
    [ reflexivity | intros y Hy; apply He; right; exact Hy ].
Qed.

Lemma Zsum_sub : forall f h l,
  Zsum (fun x => f x - h x) l = Zsum f l - Zsum h l.
Proof.
  intros f h l. induction l as [| x l IH]; [ reflexivity | ].
  rewrite !Zsum_cons, IH. ring.
Qed.

Lemma Zsum_scale : forall c f l, Zsum (fun x => c * f x) l = c * Zsum f l.
Proof.
  intros c f l. induction l as [| x l IH]; [ cbn; ring | ].
  rewrite !Zsum_cons, IH. ring.
Qed.

Lemma Zsum_const : forall c l, Zsum (fun _ => c) l = Z.of_nat (length l) * c.
Proof.
  intros c l. induction l as [| x l IH]; [ cbn; ring | ].
  rewrite Zsum_cons, IH. cbn [length]. lia.
Qed.

Lemma Zsum_dvd_diff : forall d f h l,
  (forall x, In x l -> (d | f x - h x)) -> (d | Zsum f l - Zsum h l).
Proof.
  intros d f h l. induction l as [| x l IH]; intro He.
  - exists 0. cbn. ring.
  - rewrite !Zsum_cons.
    destruct (He x (or_introl eq_refl)) as [c Hc].
    destruct (IH ltac:(intros y Hy; apply He; right; exact Hy)) as [e He2].
    exists (c + e). lia.
Qed.

Lemma fold_Zadd_perm : forall l1 l2 : list Z, Permutation l1 l2 ->
  fold_right Z.add 0 l1 = fold_right Z.add 0 l2.
Proof.
  intros l1 l2 H. induction H.
  - reflexivity.
  - cbn [fold_right]. rewrite IHPermutation. reflexivity.
  - cbn [fold_right]. ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

(* the bridge to Z[om]-valued sums *)
Lemma eZ_Zsum : forall f l, Esum (fun t => eZ (f t)) l = eZ (Zsum f l).
Proof.
  intros f l. induction l as [| x l IH]; [ reflexivity | ].
  rewrite Esum_cons, IH, Zsum_cons, eZ_add. reflexivity.
Qed.

(* congruence mod pi is compatible with sums *)
Lemma econg_add : forall pi a b c d,
  econg pi a b -> econg pi c d -> econg pi (eadd a c) (eadd b d).
Proof.
  intros pi a b c d H1 H2. unfold econg in *.
  assert (E : esub (eadd a c) (eadd b d) = eadd (esub a b) (esub c d)) by ring.
  rewrite E. apply edvd_add; assumption.
Qed.

Lemma econg_Esum : forall pi F G l,
  (forall x, In x l -> econg pi (F x) (G x)) ->
  econg pi (Esum F l) (Esum G l).
Proof.
  intros pi F G l. induction l as [| x l IH]; intro He.
  - apply econg_refl.
  - rewrite !Esum_cons. apply econg_add;
      [ apply He; left; reflexivity
      | apply IH; intros y Hy; apply He; right; exact Hy ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  power sums over F_p                                            *)
(* ----------------------------------------------------------------- *)
Section PowerSums.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.

Notation P := (Z.of_nat p).

Lemma Zpow_cong : forall (x y : Z) (n : nat),
  (P | x - y) -> (P | x ^ Z.of_nat n - y ^ Z.of_nat n).
Proof.
  intros x y n H. induction n as [| n IH].
  - exists 0. cbn. ring.
  - rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    destruct IH as [c Hc]. destruct H as [e He].
    exists (x * c + y ^ Z.of_nat n * e).
    assert (E : x * x ^ Z.of_nat n - y * y ^ Z.of_nat n
                = x * (x ^ Z.of_nat n - y ^ Z.of_nat n)
                  + y ^ Z.of_nat n * (x - y)) by ring.
    rewrite E, Hc, He. ring.
Qed.

Lemma mulmod_perm0 : forall g, ~ Nat.divide p g ->
  Permutation (map (fun x => (g * x) mod p)%nat (seq 0 p)) (seq 0 p).
Proof.
  intros g Hg. apply NoDup_Permutation_bis.
  - apply NoDup_map_inj; [ | apply seq_NoDup ].
    intros x y Hx Hy Hxy. apply in_seq in Hx. apply in_seq in Hy.
    pose proof (cancel_mod p g x y Hp Hg Hxy) as Hm.
    rewrite (Nat.mod_small x p), (Nat.mod_small y p) in Hm by lia. exact Hm.
  - rewrite length_map. lia.
  - intros z Hz. apply in_map_iff in Hz as [x [Hx _]]. rewrite <- Hx.
    apply in_seq. pose proof (Nat.mod_upper_bound (g * x)%nat p ltac:(lia)). lia.
Qed.

Lemma Zsum_reindex0 : forall f g, ~ Nat.divide p g ->
  Zsum f (seq 0 p) = Zsum (fun x => f ((g * x) mod p)%nat) (seq 0 p).
Proof.
  intros f g Hg. symmetry. unfold Zsum.
  rewrite <- (map_map (fun x => (g * x) mod p)%nat f).
  apply fold_Zadd_perm, Permutation_map, mulmod_perm0. exact Hg.
Qed.

Lemma cgmod0 : forall a : nat, (P | Z.of_nat (a mod p) - Z.of_nat a).
Proof.
  intro a. exists (- Z.of_nat (a / p)).
  assert (E : (a = p * (a / p) + a mod p)%nat) by apply Nat.div_mod_eq. lia.
Qed.

Theorem power_sum : forall a : nat, (a < p - 1)%nat ->
  (P | Zsum (fun t => (Z.of_nat t) ^ (Z.of_nat a)) (seq 0 p)).
Proof.
  intros a Ha.
  destruct (Nat.eq_dec a 0) as [-> | Ha0].
  - assert (E : forall x, In x (seq 0 p) -> (Z.of_nat x) ^ (Z.of_nat 0) = 1)
      by (intros x _; reflexivity).
    rewrite (Zsum_ext _ _ _ E), Zsum_const, length_seq.
    exists 1. ring.
  - destruct (units_cyclic p Hp) as [g [Hg Hgord]].
    set (A := Z.of_nat a). set (G := Z.of_nat g).
    set (S := Zsum (fun t => (Z.of_nat t) ^ A) (seq 0 p)).
    assert (Hgd : ~ Nat.divide p g) by (apply unit_not_div; lia).
    assert (Hre : S = Zsum (fun t => (Z.of_nat ((g * t) mod p)%nat) ^ A) (seq 0 p)).
    { unfold S. exact (Zsum_reindex0 (fun t => (Z.of_nat t) ^ A) g Hgd). }
    assert (Hscale : Zsum (fun t => G ^ A * (Z.of_nat t) ^ A) (seq 0 p) = G ^ A * S).
    { unfold S. exact (Zsum_scale (G ^ A) (fun t => (Z.of_nat t) ^ A) (seq 0 p)). }
    assert (Hcong : (P | Zsum (fun t => (Z.of_nat ((g * t) mod p)%nat) ^ A) (seq 0 p)
                         - Zsum (fun t => G ^ A * (Z.of_nat t) ^ A) (seq 0 p))).
    { apply Zsum_dvd_diff. intros x _.
      assert (Hb : (P | Z.of_nat ((g * x) mod p)%nat - G * Z.of_nat x)).
      { destruct (cgmod0 (g * x)%nat) as [c Hc]. exists c.
        rewrite Nat2Z.inj_mul in Hc. unfold G. lia. }
      pose proof (Zpow_cong _ _ a Hb) as Hd.
      assert (E : (G * Z.of_nat x) ^ Z.of_nat a = G ^ A * (Z.of_nat x) ^ A)
        by (unfold A; apply Z.pow_mul_l).
      rewrite E in Hd. exact Hd. }
    (* so p divides (1 - G^A) . S *)
    assert (Hkey : (P | (1 - G ^ A) * S)).
    { assert (E : (1 - G ^ A) * S = S - G ^ A * S) by ring.
      rewrite E, <- Hscale, Hre at 1. exact Hcong. }
    assert (HnG : ~ (P | 1 - G ^ A)).
    { intro Hd.
      assert (Hpw : pw p g a = 1%nat).
      { apply Nat2Z.inj. unfold pw.
        rewrite Nat2Z.inj_mod, Nat2Z.inj_pow.
        replace (Z.of_nat 1) with 1 by reflexivity.
        destruct Hd as [c Hc].
        replace (Z.of_nat g ^ Z.of_nat a) with (1 + (- c) * P)
          by (unfold G, A in Hc; lia).
        rewrite Z.mod_add by lia. apply Z.mod_1_l; lia. }
      pose proof (ord_divides p g a Hp Hg Hpw) as Hdv.
      rewrite Hgord in Hdv. destruct Hdv as [m Hm].
      destruct m as [| m]; [ lia | nia ]. }
    destruct (prime_mult P Hp _ _ Hkey) as [H | H]; [ contradiction | exact H ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  low-degree polynomial sums vanish                              *)
(* ----------------------------------------------------------------- *)
Theorem poly_sum : forall (b a : nat), (a + b < p - 1)%nat ->
  (P | Zsum (fun t => (Z.of_nat t) ^ (Z.of_nat a)
                      * (1 - Z.of_nat t) ^ (Z.of_nat b)) (seq 0 p)).
Proof.
  induction b as [| b IH]; intros a Hab.
  - assert (E : forall x, In x (seq 0 p) ->
              (Z.of_nat x) ^ (Z.of_nat a) * (1 - Z.of_nat x) ^ (Z.of_nat 0)
              = (Z.of_nat x) ^ (Z.of_nat a)) by (intros x _; cbn; ring).
    rewrite (Zsum_ext _ _ _ E). apply power_sum. lia.
  - assert (E : forall x, In x (seq 0 p) ->
              (Z.of_nat x) ^ (Z.of_nat a) * (1 - Z.of_nat x) ^ (Z.of_nat (S b))
              = (Z.of_nat x) ^ (Z.of_nat a) * (1 - Z.of_nat x) ^ (Z.of_nat b)
                - (Z.of_nat x) ^ (Z.of_nat (a + 1))
                  * (1 - Z.of_nat x) ^ (Z.of_nat b)).
    { intros x _.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      replace (Z.of_nat (a + 1)) with (Z.succ (Z.of_nat a)) by lia.
      rewrite Z.pow_succ_r by lia. ring. }
    rewrite (Zsum_ext _ _ _ E), Zsum_sub.
    apply Z.divide_sub_r; apply IH; lia.
Qed.

End PowerSums.

(* ----------------------------------------------------------------- *)
(*  D.  pi divides the Jacobi sum                                      *)
(* ----------------------------------------------------------------- *)
Section PiDivJ.

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
Notation kk := ((p - 1) / 3)%nat.

Lemma kk_spec : (p - 1 = 3 * kk)%nat /\ (2 <= kk)%nat.
Proof.
  destruct Hdiv as [z Hz].
  assert (Hk : (kk = z)%nat) by (rewrite Hz; apply Nat.div_mul; lia).
  rewrite Hk. lia.
Qed.

Lemma Hpip : edvd pi (eZ P).
Proof. exact (pi_dvd_p pi P Hn). Qed.

(* chi(t) is congruent to t^{(p-1)/3}, including at t = 0 *)
Lemma ch_pow : forall t : nat, (t < p)%nat ->
  econg pi (ch t) (eZ ((Z.of_nat t) ^ (Z.of_nat kk))).
Proof.
  intros t Htp. destruct kk_spec as [Hk3 Hk2].
  destruct (Nat.eq_dec t 0) as [-> | Ht0].
  - rewrite (chn_zero p pi Hp Hn).
    assert (E : (Z.of_nat 0) ^ (Z.of_nat kk) = 0) by (apply Z.pow_0_l; lia).
    rewrite E. apply econg_refl.
  - assert (Hnd : ~ edvd pi (eZ (Z.of_nat t)))
      by (apply (pi_ndvd_small p pi Hp Hp7 Hn); lia).
    pose proof (chiv_cong p pi t0 Hp Hp7 Hdiv Hn Ht (eZ (Z.of_nat t)) Hnd) as H.
    rewrite epow_eZ in H. apply econg_sym. exact H.
Qed.

Lemma ch_sb_pow : forall t : nat, (t < p)%nat ->
  econg pi (ch (sb p t)) (eZ ((1 - Z.of_nat t) ^ (Z.of_nat kk))).
Proof.
  intros t Htp.
  pose proof (ch_pow (sb p t) (sb_lt p Hp7 t)) as H1.
  assert (H2 : econg pi (eZ ((Z.of_nat (sb p t)) ^ (Z.of_nat kk)))
                        (eZ ((1 - Z.of_nat t) ^ (Z.of_nat kk)))).
  { unfold econg. rewrite <- eZ_sub.
    apply (proj2 (int_cong_iff pi P _ Hp Hn Hpip)).
    apply (Zpow_cong p Hp7).
    exact (cg_sb p Hp7 t ltac:(lia)). }
  exact (econg_trans pi _ _ _ H1 H2).
Qed.

Lemma fJ_cong : forall t : nat, (t < p)%nat ->
  econg pi (fJ p pi t)
           (eZ ((Z.of_nat t) ^ (Z.of_nat kk) * (1 - Z.of_nat t) ^ (Z.of_nat kk))).
Proof.
  intros t Htp. unfold fJ. rewrite eZ_mul.
  apply econg_mul; [ apply ch_pow | apply ch_sb_pow ]; exact Htp.
Qed.

Theorem pi_dvd_Jsum : edvd pi (Jsum p pi).
Proof.
  destruct kk_spec as [Hk3 Hk2].
  set (W := Zsum (fun t => (Z.of_nat t) ^ (Z.of_nat kk)
                           * (1 - Z.of_nat t) ^ (Z.of_nat kk)) (seq 0 p)).
  assert (HJ : econg pi (Jsum p pi) (eZ W)).
  { rewrite <- (JsumF p pi Hp Hp7 Hn).
    unfold W.
    rewrite <- (eZ_Zsum (fun t => (Z.of_nat t) ^ (Z.of_nat kk)
                                  * (1 - Z.of_nat t) ^ (Z.of_nat kk)) (seq 0 p)).
    apply econg_Esum. intros x Hx. apply in_seq in Hx. apply fJ_cong. lia. }
  assert (HW : (P | W)) by (unfold W; apply (poly_sum p Hp Hp7); lia).
  assert (HdW : edvd pi (eZ W))
    by (apply (proj2 (int_cong_iff pi P W Hp Hn Hpip)); exact HW).
  destruct HJ as [q Hq]. destruct HdW as [r Hr].
  exists (eadd q r).
  assert (E : Jsum p pi = eadd (esub (Jsum p pi) (eZ W)) (eZ W)) by ring.
  rewrite E, Hq, Hr. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  THE JACOBI SUM IS THE PRIMARY PRIME                            *)
(* ----------------------------------------------------------------- *)
Theorem jacobi_eq_primary :
  exists u, eunit u /\ primary (emul pi u) /\ Jsum p pi = emul pi u.
Proof.
  destruct (primary_prime pi P Hp ltac:(lia) Hn) as [u [Hu [Hpr _]]].
  exists u. split; [ exact Hu | split; [ exact Hpr | ] ].
  exact (Jsum_eq_primary p pi t0 Hp Hp7 Hdiv Hn Ht u Hu Hpr pi_dvd_Jsum).
Qed.

End PiDivJ.

Print Assumptions power_sum.
Print Assumptions poly_sum.
Print Assumptions pi_dvd_Jsum.
Print Assumptions jacobi_eq_primary.
