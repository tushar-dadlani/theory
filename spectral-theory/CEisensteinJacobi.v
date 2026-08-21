(* ================================================================= *)
(*  CEisensteinJacobi.v  —  reindexing, and the degenerate Jacobi sum. *)
(*                                                                    *)
(*    Esum_bij2   : reindex a sum along a bijection BETWEEN TWO lists  *)
(*    econj_Esum  : conjugation is additive over a sum                 *)
(*    chn_conj    : conj chi(s) = chi(s^{-1})                          *)
(*    chisq_sum_zero  : sum_t chi(t)^2 = 0                             *)
(*    chn_minus_one   : chi(-1) = 1                                    *)
(*    jacobi_degenerate : sum_t chi(t) conj chi(1-t) = -1              *)
(*    Jsum        : the Jacobi sum J(chi,chi), for what comes next     *)
(*                                                                    *)
(*  THE DEGENERATE JACOBI SUM IS THE ONE THAT COLLAPSES.  J(chi,lam)   *)
(*  has absolute value sqrt(p) when chi.lam is nontrivial, but when    *)
(*  lam = conj chi the product is trivial and the sum degenerates to   *)
(*  a single character sum, giving exactly -chi(-1) = -1.  It is the   *)
(*  cheap member of the family, and proving it here is deliberate:     *)
(*  it exercises the ENTIRE reindexing machinery that N(J) = p will    *)
(*  need, on a statement whose answer is already known.                *)
(*                                                                    *)
(*  THE REINDEXING IS THE POINT.  brick 2 could get away with          *)
(*  ZmodPStar.units_perm, because multiplying by a constant is a       *)
(*  permutation of F_p^* and the repo already knew it.  t |-> t/(1-t)  *)
(*  is not a permutation of anything the repo knows: it maps           *)
(*  F_p \ {0,1} ONTO F_p \ {0,-1}, two different sets of the same      *)
(*  size.  Esum_bij2 is the tool for that, and it asks only for        *)
(*  injectivity plus landing in the target -- surjectivity comes free  *)
(*  from counting, via NoDup_Permutation_bis.                          *)
(*                                                                    *)
(*  THE TWO SETS ARE CONSECUTIVE RUNS, which is a small mercy:         *)
(*  F_p \ {0,1} is seq 2 (p-2) and F_p \ {0,-1} is seq 1 (p-2), so no  *)
(*  filtering is needed anywhere and NoDup is seq_NoDup both times.    *)
(*                                                                    *)
(*  chi(-1) = 1 BECAUSE -1 IS A CUBE, namely of itself; that is the    *)
(*  cubic case being easier than the quadratic one, where the sign of  *)
(*  chi(-1) is the whole first supplementary law.                      *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot FpField
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat
        CEisensteinCubicMul CEisensteinCubicSupp CEisensteinCubicFun
        CEisensteinSum.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  reindexing along a bijection between two lists                 *)
(* ----------------------------------------------------------------- *)
Lemma Esum_bij2 : forall (f : nat -> Eis) (l1 l2 : list nat) (phi : nat -> nat),
  NoDup l1 -> (length l2 <= length l1)%nat ->
  (forall x, In x l1 -> In (phi x) l2) ->
  (forall x y, In x l1 -> In y l1 -> phi x = phi y -> x = y) ->
  Esum (fun x => f (phi x)) l1 = Esum f l2.
Proof.
  intros f l1 l2 phi Hnd Hlen Hin Hinj.
  assert (Hperm : Permutation (map phi l1) l2).
  { apply NoDup_Permutation_bis.
    - apply NoDup_map_inj; assumption.
    - rewrite length_map. exact Hlen.
    - intros z Hz. apply in_map_iff in Hz as [x [Hx Hxin]]. rewrite <- Hx.
      apply Hin; exact Hxin. }
  transitivity (Esum f (map phi l1)).
  - unfold Esum. rewrite map_map. reflexivity.
  - apply Esum_perm. exact Hperm.
Qed.

(* conjugation is additive, hence commutes with Esum *)
Lemma econj_add : forall x y, econj (eadd x y) = eadd (econj x) (econj y).
Proof. intros [a b] [c d]. unfold econj, eadd; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma econj_zero : econj ezero = ezero.
Proof. reflexivity. Qed.

Lemma econj_Esum : forall f l, econj (Esum f l) = Esum (fun x => econj (f x)) l.
Proof.
  intros f l. induction l as [| x l IH]; [ reflexivity | ].
  rewrite !Esum_cons, econj_add, IH. reflexivity.
Qed.

(* the character, as a function of a natural number *)
Definition chn (p : nat) (pi : Eis) (n : nat) : Eis := chiv p pi (eZ (Z.of_nat n)).

(* the Jacobi sum J(chi,chi), for the next brick *)
Definition Jsum (p : nat) (pi : Eis) : Eis :=
  Esum (fun t => emul (chn p pi t) (chn p pi (1 + p - t))) (seq 2 (p - 2)).

Section Jacobi.

Variable p : nat.
Variable pi : Eis.
Variable t0 : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t0) eom).

Lemma Hp2 : (2 <= p)%nat. Proof. lia. Qed.

(* multiplicativity, in the natural-number indexing *)
Lemma chn_mul : forall a b : nat,
  chn p pi ((a * b) mod p) = emul (chn p pi a) (chn p pi b).
Proof.
  intros a b. unfold chn.
  rewrite (chiv_mod p pi t0 Hp Hp7 Hdiv Hn Ht (a * b)%nat).
  rewrite Nat2Z.inj_mul, eZ_mul.
  exact (chiv_mul p pi t0 Hp Hp7 Hdiv Hn Ht _ _).
Qed.

Lemma chn_one : chn p pi 1 = eone.
Proof.
  unfold chn. replace (Z.of_nat 1) with 1 by reflexivity.
  rewrite eZ_one. exact (chiv_one p pi t0 Hp Hp7 Hdiv Hn Ht).
Qed.

Lemma chn_ndvd : forall a : nat, (1 <= a <= p - 1)%nat -> ~ edvd pi (eZ (Z.of_nat a)).
Proof. intros a Ha. exact (pi_ndvd_small p pi Hp Hp7 Hn a Ha). Qed.

Lemma chn_cuberoot : forall a : nat, (1 <= a <= p - 1)%nat -> cuberoot (chn p pi a).
Proof.
  intros a Ha. unfold chn.
  exact (chiv_cuberoot p pi Hp Hn _ (chn_ndvd a Ha)).
Qed.

Lemma chn_ne0 : forall a : nat, (1 <= a <= p - 1)%nat -> chn p pi a <> ezero.
Proof.
  intros a Ha. destruct (chn_cuberoot a Ha) as [-> | [-> | ->]]; discriminate.
Qed.

(* the conjugate of a character value is the value at the inverse *)
Lemma chn_conj : forall s : nat, (1 <= s <= p - 1)%nat ->
  econj (chn p pi s) = chn p pi (finv p s).
Proof.
  intros s Hs.
  assert (Hfi : (1 <= finv p s <= p - 1)%nat) by (apply finv_unit; assumption).
  (* chi(s) . conj chi(s) = N(chi(s)) = 1 *)
  assert (H1 : emul (chn p pi s) (econj (chn p pi s)) = eone).
  { rewrite emul_econj.
    destruct (chn_cuberoot s Hs) as [E | [E | E]]; rewrite E; reflexivity. }
  (* chi(s) . chi(s^{-1}) = chi(1) = 1 *)
  assert (H2 : emul (chn p pi s) (chn p pi (finv p s)) = eone).
  { rewrite <- chn_mul, (inv_correct p s Hp Hs). exact chn_one. }
  apply (emul_cancel (chn p pi s)); [ exact (chn_ne0 s Hs) | ].
  rewrite H1, H2. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the squared character also sums to zero                        *)
(* ----------------------------------------------------------------- *)
Theorem chisq_sum_zero :
  Esum (fun n => econj (chn p pi n)) (seq 1 (p - 1)) = ezero.
Proof.
  rewrite <- econj_Esum.
  unfold chn. rewrite (char_sum_zero p pi t0 Hp Hp7 Hdiv Hn Ht).
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  chi(-1) = 1                                                    *)
(* ----------------------------------------------------------------- *)
Theorem chn_minus_one : chn p pi (p - 1) = eone.
Proof.
  assert (Hr : (1 <= p - 1 <= p - 1)%nat) by lia.
  set (m := Z.of_nat (p - 1)).
  assert (Hnd : ~ edvd pi (eZ m)) by (unfold m; exact (chn_ndvd (p - 1)%nat Hr)).
  (* chi(m^3) = 1 by the easy half of Euler's criterion *)
  pose proof (chiv_cube p pi t0 Hp Hp7 Hdiv Hn Ht (eZ m) Hnd) as Hc.
  rewrite epow_eZ in Hc.
  (* and m^3 = -1 = p-1 mod p *)
  assert (Hcong : chiv p pi (eZ (m ^ Z.of_nat 3)) = chiv p pi (eZ m)).
  { apply (chiv_cong_eq p pi t0 Hp Hp7 Hdiv Hn Ht).
    apply (econg_eZ_of_dvd p pi Hp Hn).
    exists (Z.of_nat p * Z.of_nat p - 3 * Z.of_nat p + 2).
    unfold m. replace (Z.of_nat (p - 1)) with (Z.of_nat p - 1) by lia.
    replace (Z.of_nat 3) with 3 by reflexivity. ring. }
  unfold chn, m in *. rewrite <- Hcong. exact Hc.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE DEGENERATE JACOBI SUM                                      *)
(* ----------------------------------------------------------------- *)
Definition tmap (x : nat) : nat := (x * finv p (1 + p - x)) mod p.

Lemma tmap_range : forall x, In x (seq 2 (p - 2)) -> In (tmap x) (seq 1 (p - 2)).
Proof.
  intros x Hx. apply in_seq in Hx.
  assert (Hx2 : (2 <= x <= p - 1)%nat) by lia.
  assert (Hd : (1 <= 1 + p - x <= p - 1)%nat) by lia.
  assert (Hfi : (1 <= finv p (1 + p - x) <= p - 1)%nat) by (apply finv_unit; assumption).
  assert (Hnx : ~ Nat.divide p x) by (apply unit_not_div; lia).
  assert (Hnf : ~ Nat.divide p (finv p (1 + p - x))) by (apply unit_not_div; lia).
  assert (Hu : (1 <= tmap x <= p - 1)%nat)
    by (unfold tmap; apply mulmod_in_units; assumption).
  apply in_seq.
  (* the only thing to rule out is tmap x = p - 1, i.e. x/(1-x) = -1 *)
  assert (Hne : tmap x <> (p - 1)%nat).
  { intro Hc.
    (* then x = -(1-x) = x-1 mod p, i.e. p | 1 *)
    assert (Hmul : (((1 + p - x) * tmap x) mod p = ((1 + p - x) * (p - 1)) mod p)%nat)
      by (rewrite Hc; reflexivity).
    unfold tmap in Hmul.
    rewrite Nat.Div0.mul_mod_idemp_r in Hmul.
    assert (E : (((1 + p - x) * (x * finv p (1 + p - x)))
                = (x * ((1 + p - x) * finv p (1 + p - x))))%nat) by ring.
    rewrite E, Nat.Div0.mul_mod, (inv_correct p (1 + p - x) Hp Hd) in Hmul.
    rewrite Nat.mul_1_r, Nat.Div0.mod_mod in Hmul.
    (* so x = (1+p-x)(p-1) mod p ; in Z that says p | 1 *)
    apply (f_equal Z.of_nat) in Hmul.
    rewrite !Nat2Z.inj_mod, !Nat2Z.inj_mul in Hmul.
    assert (Hz : (Z.of_nat p | Z.of_nat x - Z.of_nat (1 + p - x) * Z.of_nat (p - 1))).
    { apply Z.mod_divide; [ lia | ].
      rewrite Zminus_mod, <- Hmul, Z.sub_diag. apply Zmod_0_l. }
    destruct Hz as [c Hc2].
    replace (Z.of_nat (1 + p - x)) with (1 + Z.of_nat p - Z.of_nat x) in Hc2 by lia.
    replace (Z.of_nat (p - 1)) with (Z.of_nat p - 1) in Hc2 by lia.
    (* the identity collapses to  (c - x + p) . p = 1, impossible *)
    assert (Hone : (c - Z.of_nat x + Z.of_nat p) * Z.of_nat p = 1).
    { replace ((c - Z.of_nat x + Z.of_nat p) * Z.of_nat p)
        with (c * Z.of_nat p
              - (Z.of_nat x - (1 + Z.of_nat p - Z.of_nat x) * (Z.of_nat p - 1)) + 1)
        by ring.
      rewrite Hc2. ring. }
    set (d := c - Z.of_nat x + Z.of_nat p) in Hone.
    destruct (Z.le_gt_cases d 0) as [Hd0 | Hd0].
    - assert (d * Z.of_nat p <= 0 * Z.of_nat p)
        by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - assert (1 * Z.of_nat p <= d * Z.of_nat p)
        by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  lia.
Qed.

Lemma tmap_inj : forall x y, In x (seq 2 (p - 2)) -> In y (seq 2 (p - 2)) ->
  tmap x = tmap y -> x = y.
Proof.
  intros x y Hx Hy He. apply in_seq in Hx. apply in_seq in Hy.
  assert (Hdx : (1 <= 1 + p - x <= p - 1)%nat) by lia.
  assert (Hdy : (1 <= 1 + p - y <= p - 1)%nat) by lia.
  (* multiply the equality by (1-x)(1-y) *)
  assert (Hkey : ((x * (1 + p - y)) mod p = (y * (1 + p - x)) mod p)%nat).
  { assert (E1 : (((( 1 + p - x) * (1 + p - y)) * tmap x) mod p
                 = (x * (1 + p - y)) mod p)%nat).
    { unfold tmap.
      rewrite Nat.Div0.mul_mod_idemp_r.
      assert (E : ((((1 + p - x) * (1 + p - y)) * (x * finv p (1 + p - x)))
                  = ((x * (1 + p - y)) * ((1 + p - x) * finv p (1 + p - x))))%nat) by ring.
      rewrite E, Nat.Div0.mul_mod, (inv_correct p (1 + p - x) Hp Hdx).
      rewrite Nat.mul_1_r, Nat.Div0.mod_mod. reflexivity. }
    assert (E2 : (((( 1 + p - x) * (1 + p - y)) * tmap y) mod p
                 = (y * (1 + p - x)) mod p)%nat).
    { unfold tmap.
      rewrite Nat.Div0.mul_mod_idemp_r.
      assert (E : ((((1 + p - x) * (1 + p - y)) * (y * finv p (1 + p - y)))
                  = ((y * (1 + p - x)) * ((1 + p - y) * finv p (1 + p - y))))%nat) by ring.
      rewrite E, Nat.Div0.mul_mod, (inv_correct p (1 + p - y) Hp Hdy).
      rewrite Nat.mul_1_r, Nat.Div0.mod_mod. reflexivity. }
    rewrite <- E1, <- E2, He. reflexivity. }
  (* x(1-y) = y(1-x) mod p  gives  x = y mod p, and both are in range *)
  apply (f_equal Z.of_nat) in Hkey.
  rewrite !Nat2Z.inj_mod, !Nat2Z.inj_mul in Hkey.
  assert (Hz : (Z.of_nat p | Z.of_nat x * Z.of_nat (1 + p - y)
                             - Z.of_nat y * Z.of_nat (1 + p - x))).
  { apply Z.mod_divide; [ lia | ].
    rewrite Zminus_mod, Hkey, Z.sub_diag. apply Zmod_0_l. }
  destruct Hz as [c Hc].
  replace (Z.of_nat (1 + p - y)) with (1 + Z.of_nat p - Z.of_nat y) in Hc by lia.
  replace (Z.of_nat (1 + p - x)) with (1 + Z.of_nat p - Z.of_nat x) in Hc by lia.
  assert (Hdiff : Z.of_nat x - Z.of_nat y
                  = (c - Z.of_nat x + Z.of_nat y) * Z.of_nat p) by nia.
  assert (Hb : - Z.of_nat p < Z.of_nat x - Z.of_nat y < Z.of_nat p) by lia.
  set (d := c - Z.of_nat x + Z.of_nat y) in *.
  assert (Hd0 : d = 0).
  { destruct (Z.lt_trichotomy d 0) as [H | [H | H]]; [ | exact H | ].
    - assert (d * Z.of_nat p <= (-1) * Z.of_nat p)
        by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - assert (1 * Z.of_nat p <= d * Z.of_nat p)
        by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  rewrite Hd0 in Hdiff. lia.
Qed.

(* the summand identity: chi(t) conj chi(1-t) = chi(t/(1-t)) *)
Lemma jacobi_term : forall x, In x (seq 2 (p - 2)) ->
  emul (chn p pi x) (econj (chn p pi (1 + p - x))) = chn p pi (tmap x).
Proof.
  intros x Hx. apply in_seq in Hx.
  assert (Hd : (1 <= 1 + p - x <= p - 1)%nat) by lia.
  rewrite (chn_conj (1 + p - x)%nat Hd).
  unfold tmap. rewrite chn_mul. reflexivity.
Qed.

Theorem jacobi_degenerate :
  Esum (fun x => emul (chn p pi x) (econj (chn p pi (1 + p - x)))) (seq 2 (p - 2))
  = eopp eone.
Proof.
  (* rewrite each term, then reindex onto seq 1 (p-2) *)
  rewrite (Esum_ext _ (fun x => chn p pi (tmap x)) _ jacobi_term).
  rewrite (Esum_bij2 (chn p pi) (seq 2 (p - 2)) (seq 1 (p - 2)) tmap
             (seq_NoDup _ _) ltac:(rewrite !length_seq; lia) tmap_range tmap_inj).
  (* and seq 1 (p-1) = seq 1 (p-2) ++ [p-1] *)
  assert (Hsplit : seq 1 (p - 1) = seq 1 (p - 2) ++ [(p - 1)%nat]).
  { replace (p - 1)%nat with (S (p - 2)) at 1 by lia.
    rewrite seq_S.
    replace (1 + (p - 2))%nat with (p - 1)%nat by lia. reflexivity. }
  assert (Happ : forall f l1 l2, Esum f (l1 ++ l2) = eadd (Esum f l1) (Esum f l2)).
  { intros f l1 l2. induction l1 as [| a l1 IH]; [ cbn; unfold Esum; cbn; ring | ].
    cbn [app]. rewrite !Esum_cons, IH. ring. }
  pose proof (char_sum_zero p pi t0 Hp Hp7 Hdiv Hn Ht) as Hzero.
  change (Esum (fun n => chiv p pi (eZ (Z.of_nat n))) (seq 1 (p - 1)))
    with (Esum (chn p pi) (seq 1 (p - 1))) in Hzero.
  rewrite Hsplit, Happ in Hzero.
  assert (Hlast : Esum (chn p pi) [(p - 1)%nat] = eone).
  { rewrite Esum_cons, Esum_nil, chn_minus_one. ring. }
  rewrite Hlast in Hzero.
  (* S + 1 = 0 *)
  assert (E : Esum (chn p pi) (seq 1 (p - 2))
              = esub (eadd (Esum (chn p pi) (seq 1 (p - 2))) eone) eone) by ring.
  rewrite E, Hzero. unfold esub. ring.
Qed.

End Jacobi.

Print Assumptions Esum_bij2.
Print Assumptions chn_conj.
Print Assumptions chn_minus_one.
Print Assumptions jacobi_degenerate.
