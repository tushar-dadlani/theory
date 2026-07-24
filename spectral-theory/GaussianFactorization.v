(* ================================================================= *)
(*  GaussianFactorization.v                                          *)
(*                                                                    *)
(*  EXISTENCE OF FACTORISATION INTO IRREDUCIBLES in Z[i].            *)
(*                                                                    *)
(*  Every nonzero non-unit is a product of irreducibles.  Combined    *)
(*  with Euclid's lemma (GaussianIrreducible) this is unique          *)
(*  factorisation for Z[i].                                          *)
(*                                                                    *)
(*  Constructive (axiom-free): the nearest-integer quotient is EXACT   *)
(*  when a | z (ZIdiv_exact), so divisibility is DECIDABLE without a   *)
(*  search; a bounded search over the box {N(a) <= N(z)} then finds a  *)
(*  proper divisor or certifies irreducibility.  Strong induction on   *)
(*  the norm assembles the factorisation.                            *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia List Bool Wf_nat.
Require Import GaussianIntegers GaussianDivision GaussianGCD GaussianIrreducible.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(*  §1  exact division  =>  decidable divisibility                    *)
(* ================================================================= *)

Lemma znear_exact : forall c d, 0 < d -> znear (c * d) d = c.
Proof.
  intros c d Hd; unfold znear; symmetry.
  apply (Z.div_unique_pos (2 * (c * d) + d) (2 * d) c d); [ lia | ring ].
Qed.

(* the coordinates of  c * (d as a Gaussian integer) *)
Lemma zRe_mul_ZtoZI : forall c d, zRe (ZImul c (ZtoZI d)) = zRe c * d.
Proof. intros c d; unfold ZImul, ZImulg, ZtoZI; cbn [zRe zIm]; ring. Qed.

Lemma zIm_mul_ZtoZI : forall c d, zIm (ZImul c (ZtoZI d)) = zIm c * d.
Proof. intros c d; unfold ZImul, ZImulg, ZtoZI; cbn [zRe zIm]; ring. Qed.

Lemma ZIdiv_exact : forall z a c, a <> ZI0 -> z = ZImul a c -> ZIdiv z a = c.
Proof.
  intros z a c Ha Hz.
  assert (Hd : 0 < ZInorm (-1) a) by (apply norm_pos; exact Ha).
  assert (Hp : ZImul z (ZIconj a) = ZImul c (ZtoZI (ZInorm (-1) a))).
  { rewrite Hz.
    replace (ZImul (ZImul a c) (ZIconj a)) with (ZImul c (ZImul a (ZIconj a))) by ring.
    unfold ZImul; rewrite ZImulg_conj; reflexivity. }
  unfold ZIdiv; rewrite Hp, zRe_mul_ZtoZI, zIm_mul_ZtoZI, !znear_exact by exact Hd.
  apply ZIeq; reflexivity.
Qed.

(* boolean equality on ZI *)
Definition ZIeqb (a b : ZI) : bool := (zRe a =? zRe b) && (zIm a =? zIm b).

Lemma ZIeqb_eq : forall a b, ZIeqb a b = true <-> a = b.
Proof.
  intros a b; unfold ZIeqb; rewrite andb_true_iff, !Z.eqb_eq; split.
  - intros [H1 H2]; apply ZIeq; assumption.
  - intros ->; split; reflexivity.
Qed.

(* total boolean divisibility test (correct for a <> 0) *)
Definition ZIdvdb (a z : ZI) : bool := ZIeqb z (ZImul a (ZIdiv z a)).

Lemma ZIdvdb_spec : forall a z, a <> ZI0 -> (ZIdvdb a z = true <-> ZIdvd a z).
Proof.
  intros a z Ha; unfold ZIdvdb; rewrite ZIeqb_eq; split.
  - intro H; exists (ZIdiv z a); exact H.
  - intros [c Hc]; rewrite (ZIdiv_exact z a c Ha Hc); exact Hc.
Qed.

Lemma ZIdvd_dec : forall a z, a <> ZI0 -> {ZIdvd a z} + {~ ZIdvd a z}.
Proof.
  intros a z Ha; destruct (ZIdvdb a z) eqn:E.
  - left; apply (ZIdvdb_spec a z Ha); exact E.
  - right; intro H; apply (ZIdvdb_spec a z Ha) in H; rewrite H in E; discriminate.
Qed.

(* ================================================================= *)
(*  §2  a bounded box of Gaussian integers                           *)
(* ================================================================= *)

Definition zrange (B : nat) : list Z :=
  map (fun k => Z.of_nat k - Z.of_nat B) (seq 0 (2 * B + 1)%nat).

Definition gbox (B : nat) : list ZI :=
  map (fun xy => mkZI (fst xy) (snd xy)) (list_prod (zrange B) (zrange B)).

Lemma zrange_spec : forall B z, In z (zrange B) <-> (- Z.of_nat B <= z <= Z.of_nat B).
Proof.
  intros B z; unfold zrange; rewrite in_map_iff; split.
  - intros [k [Hk Hin]]; apply in_seq in Hin; subst z; lia.
  - intro Hz; exists (Z.to_nat (z + Z.of_nat B)); split.
    + rewrite Z2Nat.id by lia; ring.
    + apply in_seq.
      assert (0 <= z + Z.of_nat B) by lia.
      assert (z + Z.of_nat B <= 2 * Z.of_nat B) by lia.
      lia.
Qed.

Lemma gbox_spec : forall B a,
  In a (gbox B) <-> (In (zRe a) (zrange B) /\ In (zIm a) (zrange B)).
Proof.
  intros B a; unfold gbox; rewrite in_map_iff; split.
  - intros [[x y] [Hxy Hin]]; cbn [fst snd] in Hxy; subst a;
      apply in_prod_iff in Hin; cbn [zRe zIm]; exact Hin.
  - intros [Hx Hy]; exists (zRe a, zIm a); cbn [fst snd]; split.
    + destruct a; reflexivity.
    + apply in_prod_iff; split; assumption.
Qed.

Lemma abs_le_sqrt : forall t n, t * t <= n -> 0 <= n -> - Z.sqrt n <= t <= Z.sqrt n.
Proof.
  intros t n Ht Hn.
  assert (Habs : Z.abs t * Z.abs t = t * t)
    by (destruct (Z.abs_spec t) as [[_ E]|[_ E]]; rewrite E; ring).
  assert (Hle : Z.abs t <= Z.sqrt n)
    by (apply (proj1 (Z.sqrt_le_square n (Z.abs t) Hn (Z.abs_nonneg t))); rewrite Habs; exact Ht).
  lia.
Qed.

Lemma in_gbox_of_norm_le : forall a z,
  ZInorm (-1) a <= ZInorm (-1) z ->
  In a (gbox (Z.to_nat (Z.sqrt (ZInorm (-1) z)))).
Proof.
  intros a z Hle.
  assert (Hn0 : 0 <= ZInorm (-1) z) by apply ZInorm_nonneg.
  assert (Hsq : Z.of_nat (Z.to_nat (Z.sqrt (ZInorm (-1) z))) = Z.sqrt (ZInorm (-1) z))
    by (apply Z2Nat.id; apply Z.sqrt_nonneg).
  rewrite gbox_spec, !zrange_spec, Hsq.
  rewrite ZInorm_neg1 in Hle.
  split; apply abs_le_sqrt; solve [ nia | exact Hn0 ].
Qed.

(* ================================================================= *)
(*  §3  proper-divisor search: reducible witness or irreducibility    *)
(* ================================================================= *)

Definition pdivb (z a : ZI) : bool :=
  (1 <? ZInorm (-1) a) && (ZInorm (-1) a <? ZInorm (-1) z) && ZIdvdb a z.

Definition pdiv_list (z : ZI) : list ZI :=
  filter (pdivb z) (gbox (Z.to_nat (Z.sqrt (ZInorm (-1) z)))).

Lemma norm_ZI0 : ZInorm (-1) ZI0 = 0.
Proof. reflexivity. Qed.

Lemma pdiv_list_correct : forall z a, In a (pdiv_list z) ->
  ZIdvd a z /\ 1 < ZInorm (-1) a /\ ZInorm (-1) a < ZInorm (-1) z.
Proof.
  intros z a Hin; unfold pdiv_list in Hin; apply filter_In in Hin.
  destruct Hin as [_ Hb]; unfold pdivb in Hb.
  rewrite !andb_true_iff in Hb; destruct Hb as [[H1 H2] Hd].
  apply Z.ltb_lt in H1; apply Z.ltb_lt in H2.
  assert (Ha : a <> ZI0) by (intro Heq; subst a; rewrite norm_ZI0 in H1; lia).
  split; [ apply (ZIdvdb_spec a z Ha); exact Hd | split; [ exact H1 | exact H2 ] ].
Qed.

Lemma pdiv_nil_irreducible : forall z,
  z <> ZI0 -> ~ ZIunit z -> pdiv_list z = [] -> ZIirreducible z.
Proof.
  intros z Hz Hu Hnil; split; [ exact Hu | split; [ exact Hz | ] ].
  intros a b Hab.
  destruct (Z.eq_dec (ZInorm (-1) a) 1) as [Hua | Hna];
    [ left; apply ZIunit_norm; exact Hua | ].
  destruct (Z.eq_dec (ZInorm (-1) b) 1) as [Hub | Hnb];
    [ right; apply ZIunit_norm; exact Hub | ].
  exfalso.
  assert (Ha : a <> ZI0) by (intro Heq; apply Hz; rewrite Hab, Heq; ring).
  assert (Hb : b <> ZI0) by (intro Heq; apply Hz; rewrite Hab, Heq; ring).
  pose proof (norm_pos a Ha); pose proof (norm_pos b Hb).
  assert (Hnorm : ZInorm (-1) a * ZInorm (-1) b = ZInorm (-1) z)
    by (symmetry; rewrite Hab; unfold ZImul; apply ZInorm_mul).
  assert (Hmem : In a (pdiv_list z)).
  { unfold pdiv_list; apply filter_In; split.
    - apply in_gbox_of_norm_le; nia.
    - unfold pdivb; rewrite !andb_true_iff; repeat split.
      + apply Z.ltb_lt; lia.
      + apply Z.ltb_lt; nia.
      + apply (ZIdvdb_spec a z Ha); exists b; exact Hab. }
  rewrite Hnil in Hmem; exact (in_nil Hmem).
Qed.

(* ================================================================= *)
(*  §4  EXISTENCE of factorisation into irreducibles                 *)
(* ================================================================= *)

Fixpoint ZIprod (l : list ZI) : ZI :=
  match l with [] => ZI1 | x :: t => ZImul x (ZIprod t) end.

Lemma ZIprod_app : forall l1 l2, ZIprod (l1 ++ l2) = ZImul (ZIprod l1) (ZIprod l2).
Proof. induction l1 as [|a l1 IH]; intro l2; simpl; [ ring | rewrite IH; ring ]. Qed.

Theorem factor_exists : forall z, z <> ZI0 -> ~ ZIunit z ->
  exists l, (forall p, In p l -> ZIirreducible p) /\ z = ZIprod l.
Proof.
  intro z; induction z as [z IH] using
    (well_founded_induction (well_founded_ltof _ (fun w => Z.to_nat (ZInorm (-1) w)))).
  intros Hz Hu.
  destruct (pdiv_list z) as [|d rest] eqn:E.
  - (* no proper divisor : z is irreducible *)
    exists [z]; split; [ | simpl; ring ].
    intros p [<-|[]]; apply pdiv_nil_irreducible; [ exact Hz | exact Hu | exact E ].
  - (* d is a proper divisor : split and recurse *)
    assert (Hd_in : In d (pdiv_list z)) by (rewrite E; left; reflexivity).
    destruct (pdiv_list_correct z d Hd_in) as [Hdz [Hd1 Hd2]].
    assert (Hd0 : d <> ZI0) by (intro Heq; subst d; rewrite norm_ZI0 in Hd1; lia).
    assert (Hdu : ~ ZIunit d) by (rewrite ZIunit_norm; lia).
    destruct Hdz as [c Hc].
    assert (Hc0 : c <> ZI0) by (intro Heq; apply Hz; rewrite Hc, Heq; ring).
    pose proof (norm_pos d Hd0); pose proof (norm_pos c Hc0).
    assert (Hnorm : ZInorm (-1) d * ZInorm (-1) c = ZInorm (-1) z)
      by (symmetry; rewrite Hc; unfold ZImul; apply ZInorm_mul).
    assert (Hcu : ~ ZIunit c) by (rewrite ZIunit_norm; intro Hc1; nia).
    assert (Hd_lt : ltof _ (fun w => Z.to_nat (ZInorm (-1) w)) d z)
      by (unfold ltof;
          apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg d) (ZInorm_nonneg z))); exact Hd2).
    assert (Hc_lt : ltof _ (fun w => Z.to_nat (ZInorm (-1) w)) c z)
      by (unfold ltof;
          apply (proj1 (Z2Nat.inj_lt _ _ (ZInorm_nonneg c) (ZInorm_nonneg z))); nia).
    destruct (IH d Hd_lt Hd0 Hdu) as [ld [Hld Hldp]].
    destruct (IH c Hc_lt Hc0 Hcu) as [lc [Hlc Hlcp]].
    exists (ld ++ lc); split.
    + intros p Hp; apply in_app_or in Hp; destruct Hp; [ apply Hld | apply Hlc ]; assumption.
    + rewrite ZIprod_app, <- Hldp, <- Hlcp; exact Hc.
Qed.

Print Assumptions factor_exists.

(* ================================================================= *)
(*  END GaussianFactorization.v                                      *)
(*  Every nonzero non-unit of Z[i] is a product of irreducibles       *)
(*  (factor_exists), by strong induction on the norm: exact division   *)
(*  makes divisibility decidable (ZIdiv_exact / ZIdvd_dec), a bounded  *)
(*  box search finds a proper divisor or certifies irreducibility,     *)
(*  and the two smaller factors recurse.  With Euclid's lemma          *)
(*  (GaussianIrreducible) this gives unique factorisation in Z[i].     *)
(*  Closed under the global context (axiom-free).                     *)
(* ================================================================= *)
