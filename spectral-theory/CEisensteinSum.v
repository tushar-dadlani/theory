(* ================================================================= *)
(*  CEisensteinSum.v  —  sums over F_p with values in Z[om].           *)
(*                                                                    *)
(*    Esum f l        : sum of f over a list of indices                *)
(*    Esum_perm       : the sum is permutation-invariant               *)
(*    Esum_reindex_mul: reindexing F_p^* by multiplication             *)
(*    chiv_cong_eq    : chi depends only on the class mod pi           *)
(*    chiv_nontrivial : a primitive root is not a cube                 *)
(*    char_sum_zero   : sum_{t=1}^{p-1} chi(t) = 0                     *)
(*                                                                    *)
(*  THIS IS THE ORTHOGONALITY THE WHOLE SUM LAYER RESTS ON.  Every     *)
(*  identity about Gauss and Jacobi sums is, at bottom, the statement  *)
(*  that a nontrivial character sums to zero over the group, and the   *)
(*  proof is the oldest trick there is: multiply the index by a fixed  *)
(*  c, which permutes F_p^* and pulls chi(c) out front, so             *)
(*  S = chi(c) S and (1 - chi(c)) S = 0.  Z[om] is a domain, so if     *)
(*  chi(c) <> 1 then S = 0.                                            *)
(*                                                                    *)
(*  THE PERMUTATION IS ALREADY IN THE REPO and is reused verbatim:     *)
(*  ZmodPStar.units_perm is a statement about lists of naturals, with  *)
(*  no complex numbers anywhere in it, so the Gauss-sum layer over C   *)
(*  and this layer over Z[om] share it.  What could not be shared is   *)
(*  the sum itself -- GaussSum.Sf folds Cadd -- so Esum re-does the    *)
(*  fold algebra over Eis.  That is deliberate duplication: the ring   *)
(*  is different, and there is no common structure in the development  *)
(*  to abstract over.                                                  *)
(*                                                                    *)
(*  FINDING c IS WHERE THE PREVIOUS BRICK IS SPENT.  chi is nontrivial *)
(*  exactly because a non-cube exists, and the cleanest witness is a   *)
(*  primitive root g: if chi(g) were 1 then g^{(p-1)/3} = 1, so the    *)
(*  order of g would be at most (p-1)/3, not p-1.  units_cyclic        *)
(*  supplies g and ord_least closes it -- no appeal to counting cubes. *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat
        CEisensteinCubicMul CEisensteinCubicSupp CEisensteinCubicFun.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the sum, and its fold algebra                                  *)
(* ----------------------------------------------------------------- *)
Definition Esum (f : nat -> Eis) (l : list nat) : Eis :=
  fold_right eadd ezero (map f l).

Lemma Esum_nil : forall f, Esum f [] = ezero.
Proof. reflexivity. Qed.

Lemma Esum_cons : forall f x l, Esum f (x :: l) = eadd (f x) (Esum f l).
Proof. reflexivity. Qed.

Lemma Esum_ext : forall f h l,
  (forall x, In x l -> f x = h x) -> Esum f l = Esum h l.
Proof.
  intros f h l. induction l as [| x l IH]; intro He; [ reflexivity | ].
  rewrite !Esum_cons, (He x (or_introl eq_refl)), IH;
    [ reflexivity | intros y Hy; apply He; right; exact Hy ].
Qed.

Lemma Esum_scale_l : forall c f l,
  Esum (fun x => emul c (f x)) l = emul c (Esum f l).
Proof.
  intros c f l. induction l as [| x l IH]; [ cbn; ring | ].
  rewrite !Esum_cons, IH. ring.
Qed.

Lemma fold_eadd_perm : forall l1 l2 : list Eis, Permutation l1 l2 ->
  fold_right eadd ezero l1 = fold_right eadd ezero l2.
Proof.
  intros l1 l2 H. induction H.
  - reflexivity.
  - cbn [fold_right]. rewrite IHPermutation. reflexivity.
  - cbn [fold_right]. ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Lemma Esum_perm : forall f l1 l2, Permutation l1 l2 -> Esum f l1 = Esum f l2.
Proof.
  intros f l1 l2 H. unfold Esum. apply fold_eadd_perm, Permutation_map, H.
Qed.

Lemma Esum_reindex_mul : forall f b p,
  prime (Z.of_nat p) -> ~ Nat.divide p b ->
  Esum f (seq 1 (p - 1)) = Esum (fun x => f ((b * x) mod p)%nat) (seq 1 (p - 1)).
Proof.
  intros f b p Hp Hb. unfold Esum.
  rewrite <- (map_map (fun x => (b * x) mod p)%nat f).
  apply fold_eadd_perm, Permutation_map, Permutation_sym, units_perm; assumption.
Qed.

Lemma esub_eq_zero : forall x y, esub x y = ezero -> x = y.
Proof.
  intros x y H.
  assert (E : x = eadd (esub x y) y) by ring.
  rewrite E, H. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the character depends only on the residue class                *)
(* ----------------------------------------------------------------- *)
Section Sums.

Variable p : nat.
Variable pi : Eis.
Variable t : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t) eom).

Lemma Hpi0 : pi <> ezero.
Proof. exact (pi_ne0 p pi Hp Hn). Qed.

Lemma Hpip : edvd pi (eZ (Z.of_nat p)).
Proof. exact (pi_dvd_p pi (Z.of_nat p) Hn). Qed.

Theorem chiv_cong_eq : forall a b, econg pi a b -> chiv p pi a = chiv p pi b.
Proof.
  intros a b Hab.
  destruct (Eis_dec (erem a pi) ezero) as [Ea | Ea].
  { assert (Ha : edvd pi a) by (apply (edvd_rem pi a Hpi0); exact Ea).
    assert (Hb : edvd pi b).
    { assert (E : b = esub a (esub a b)) by ring.
      rewrite E. apply edvd_sub; assumption. }
    rewrite (chiv_zero p pi Hp Hn a Ha), (chiv_zero p pi Hp Hn b Hb). reflexivity. }
  assert (Ha : ~ edvd pi a) by (intro Hc; apply Ea, (edvd_rem pi a Hpi0); exact Hc).
  assert (Hb : ~ edvd pi b).
  { intro Hc. apply Ha.
    assert (E : a = eadd (esub a b) b) by ring.
    rewrite E. apply edvd_add; assumption. }
  apply (cuberoot_unique pi (Z.of_nat p) (epow a ((p - 1) / 3))).
  - exact Hn.
  - lia.
  - exact (chiv_cuberoot p pi Hp Hn a Ha).
  - exact (chiv_cuberoot p pi Hp Hn b Hb).
  - exact (chiv_cong p pi t Hp Hp7 Hdiv Hn Ht a Ha).
  - apply (econg_trans pi _ (epow b ((p - 1) / 3)) _).
    + apply econg_pow. exact Hab.
    + exact (chiv_cong p pi t Hp Hp7 Hdiv Hn Ht b Hb).
Qed.

(* integers congruent mod p have the same character *)
Lemma econg_eZ_of_dvd : forall m n, (Z.of_nat p | m - n) -> econg pi (eZ m) (eZ n).
Proof.
  intros m n H. unfold econg. rewrite <- eZ_sub.
  apply (proj2 (int_cong_iff pi (Z.of_nat p) (m - n) Hp Hn Hpip)). exact H.
Qed.

Lemma chiv_mod : forall n : nat,
  chiv p pi (eZ (Z.of_nat (n mod p))) = chiv p pi (eZ (Z.of_nat n)).
Proof.
  intro n. apply chiv_cong_eq, econg_eZ_of_dvd.
  exists (- Z.of_nat (n / p)).
  assert (E : (n = p * (n / p) + n mod p)%nat) by (apply Nat.div_mod_eq).
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  nontriviality: a primitive root is not a cube                  *)
(* ----------------------------------------------------------------- *)
Lemma pi_ndvd_small : forall a : nat, (1 <= a <= p - 1)%nat ->
  ~ edvd pi (eZ (Z.of_nat a)).
Proof.
  intros a Ha Hc.
  apply (proj1 (int_cong_iff pi (Z.of_nat p) (Z.of_nat a) Hp Hn Hpip)) in Hc.
  destruct Hc as [c Hc].
  assert (HPa : 0 < Z.of_nat a < Z.of_nat p) by lia.
  destruct (Z.le_gt_cases c 0) as [Hc0 | Hc0].
  - assert (c * Z.of_nat p <= 0 * Z.of_nat p) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - assert (1 * Z.of_nat p <= c * Z.of_nat p) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma econg_eone_pw : forall (a k : nat), (1 <= a <= p - 1)%nat ->
  econg pi (epow (eZ (Z.of_nat a)) k) eone -> pw p a k = 1%nat.
Proof.
  intros a k Ha H.
  rewrite epow_eZ in H.
  assert (Hd : (Z.of_nat p | Z.of_nat a ^ Z.of_nat k - 1)).
  { apply (proj1 (int_cong_iff pi (Z.of_nat p) _ Hp Hn Hpip)).
    unfold econg in H. rewrite <- eZ_one, <- eZ_sub in H. exact H. }
  apply Nat2Z.inj. unfold pw.
  rewrite Nat2Z.inj_mod, Nat2Z.inj_pow.
  replace (Z.of_nat 1) with 1 by reflexivity.
  destruct Hd as [c Hc].
  replace (Z.of_nat a ^ Z.of_nat k) with (1 + c * Z.of_nat p) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_1_l; lia.
Qed.

Theorem chiv_nontrivial :
  exists c : nat, (1 <= c <= p - 1)%nat /\ chiv p pi (eZ (Z.of_nat c)) <> eone.
Proof.
  destruct (units_cyclic p Hp) as [g [Hg Hgord]].
  exists g. split; [ exact Hg | ].
  intro Hc.
  (* chi(g) = 1 would make g^{(p-1)/3} congruent to 1 *)
  assert (Hcong : econg pi (epow (eZ (Z.of_nat g)) ((p - 1) / 3)) eone).
  { rewrite <- Hc.
    exact (chiv_cong p pi t Hp Hp7 Hdiv Hn Ht _ (pi_ndvd_small g Hg)). }
  pose proof (econg_eone_pw g ((p - 1) / 3)%nat Hg Hcong) as Hpw.
  destruct Hdiv as [q Hq].
  assert (Hq3 : ((p - 1) / 3 = q)%nat) by (rewrite Hq; apply Nat.div_mul; lia).
  rewrite Hq3 in Hpw.
  assert (Hle : (ord p g <= q)%nat) by (apply ord_least; [ exact Hp | exact Hg | lia | exact Hpw ]).
  rewrite Hgord in Hle. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  ORTHOGONALITY                                                  *)
(* ----------------------------------------------------------------- *)
Theorem char_sum_zero :
  Esum (fun n => chiv p pi (eZ (Z.of_nat n))) (seq 1 (p - 1)) = ezero.
Proof.
  set (S := Esum (fun n => chiv p pi (eZ (Z.of_nat n))) (seq 1 (p - 1))).
  destruct chiv_nontrivial as [c [Hc Hc1]].
  assert (Hcd : ~ Nat.divide p c).
  { intros [k Hk]. destruct k; lia. }
  (* reindex by multiplication by c *)
  assert (Hre : S = Esum (fun x => chiv p pi (eZ (Z.of_nat ((c * x) mod p)))) (seq 1 (p - 1))).
  { unfold S. exact (Esum_reindex_mul (fun n => chiv p pi (eZ (Z.of_nat n))) c p Hp Hcd). }
  (* and pull chi(c) out *)
  assert (Hpull : Esum (fun x => chiv p pi (eZ (Z.of_nat ((c * x) mod p)))) (seq 1 (p - 1))
                  = emul (chiv p pi (eZ (Z.of_nat c))) S).
  { unfold S. rewrite <- Esum_scale_l. apply Esum_ext. intros x _.
    rewrite chiv_mod, Nat2Z.inj_mul, eZ_mul.
    exact (chiv_mul p pi t Hp Hp7 Hdiv Hn Ht _ _). }
  rewrite Hpull in Hre.
  (* (1 - chi(c)) . S = 0 in a domain *)
  assert (Hz : emul (esub eone (chiv p pi (eZ (Z.of_nat c)))) S = ezero).
  { assert (E : emul (esub eone (chiv p pi (eZ (Z.of_nat c)))) S
                = esub S (emul (chiv p pi (eZ (Z.of_nat c))) S)) by ring.
    rewrite E, <- Hre. ring. }
  destruct (emul_eq_zero _ _ Hz) as [E | E]; [ | exact E ].
  exfalso. apply Hc1. symmetry. exact (esub_eq_zero _ _ E).
Qed.

Corollary char_sum_zero_full :
  Esum (fun n => chiv p pi (eZ (Z.of_nat n))) (seq 0 p) = ezero.
Proof.
  assert (Hs : seq 0 p = 0%nat :: seq 1 (p - 1))
    by (replace p with (S (p - 1)) at 1 by lia; reflexivity).
  rewrite Hs, Esum_cons, char_sum_zero.
  assert (H0 : chiv p pi (eZ (Z.of_nat 0)) = ezero).
  { apply (chiv_zero p pi Hp Hn). exists ezero. cbn [Z.of_nat]. unfold eZ, ezero. 
    apply Eis_eq; cbn [ea eb]; ring. }
  rewrite H0. ring.
Qed.

End Sums.

Print Assumptions Esum_perm.
Print Assumptions chiv_cong_eq.
Print Assumptions chiv_nontrivial.
Print Assumptions char_sum_zero.
