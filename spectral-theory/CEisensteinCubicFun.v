(* ================================================================= *)
(*  CEisensteinCubicFun.v  —  the cubic character as a FUNCTION.       *)
(*                                                                    *)
(*    edvdb       : divisibility in Z[om], decided by Euclid           *)
(*    chiv p pi a : the cubic residue symbol, as an element of Z[om]   *)
(*    chiv_cong   : it is congruent to a^{(p-1)/3}, as promised        *)
(*    chiv_mul    : chi(ab) = chi(a) chi(b), NOW AS AN EQUATION        *)
(*                                                                    *)
(*  EVERY EARLIER STATEMENT OF THE SYMBOL WAS A RELATION, NOT A VALUE. *)
(*  cubic_symbol says: exactly one of three congruences holds.        *)
(*  cubic_symbol_mul says: if u, v, w are the three values then        *)
(*  w = uv.  Both are perfectly good theorems and both are useless    *)
(*  for a Jacobi sum, because sum_t chi(t) chi(1-t) needs chi(t) to    *)
(*  be a TERM one can add up.  Turning the relation into a function    *)
(*  is the gate to everything downstream, and it is why this file      *)
(*  comes first on the road to reciprocity.                            *)
(*                                                                    *)
(*  THE FUNCTION IS BUILT WITHOUT ANY CHOICE PRINCIPLE, which was the  *)
(*  constraint the whole development runs under.  The trichotomy is    *)
(*  resolved by DECIDING the three congruences rather than by          *)
(*  selecting from an existential, and they are decidable because      *)
(*  Euclidean division is: pi divides z exactly when erem z pi is      *)
(*  zero.  That equivalence (edvd_rem) is the only new mathematics     *)
(*  here, and it is the usual argument -- if z = pi.q then the         *)
(*  remainder is pi.(q - equo), whose norm is a multiple of N(pi) yet  *)
(*  strictly below it, so the cofactor vanishes.                       *)
(*                                                                    *)
(*  chi(0) IS DEFINED TO BE 0, the standard convention, and it is what *)
(*  makes chiv_mul hold with NO hypothesis on a and b at all: when pi  *)
(*  divides a the left side is 0 because pi divides ab, and the right  *)
(*  side is 0 because chi(a) is.  That the two zeros agree is exactly  *)
(*  primality of pi (irred_prime), so the convention is not a          *)
(*  bookkeeping trick -- it is where unique factorization is spent.    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring Bool.
Require Import ZmodPStar
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD CEisensteinResidue CEisensteinFermat
        CEisensteinCubicMul CEisensteinCubicSupp.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  divisibility is decidable                                      *)
(* ----------------------------------------------------------------- *)
Lemma enorm_pos : forall z, z <> ezero -> 1 <= enorm z.
Proof.
  intros z Hz. pose proof (enorm_nonneg z) as H0.
  destruct (Z.eq_dec (enorm z) 0) as [E | E];
    [ exfalso; apply Hz; apply enorm_zero; exact E | lia ].
Qed.

Theorem edvd_rem : forall d z, d <> ezero -> (edvd d z <-> erem z d = ezero).
Proof.
  intros d z Hd. split.
  - intros [q Hq].
    destruct (euclid z d Hd) as [_ Hlt].
    assert (Hr : erem z d = emul d (esub q (equo z d)))
      by (unfold erem; rewrite Hq at 1; ring).
    assert (Hc : esub q (equo z d) = ezero).
    { destruct (Eis_dec (esub q (equo z d)) ezero) as [E | E]; [ exact E | exfalso ].
      pose proof (enorm_pos _ E) as Hge.
      rewrite Hr, enorm_mul in Hlt.
      pose proof (enorm_nonneg d) as Hdn. nia. }
    rewrite Hr, Hc. ring.
  - intro Hr. exists (equo z d).
    pose proof (euclid_eq z d) as He. rewrite Hr in He.
    rewrite He at 1. ring.
Qed.

(* the test is kept TRANSPARENT -- Eis_dec is opaque, and a chiv built
   on it would be a well-defined value that no Compute could ever
   evaluate.  Comparing coordinates with Z.eqb costs nothing and keeps
   the character executable, which is how its table gets checked. *)
Definition eeqb (z w : Eis) : bool := (ea z =? ea w)%Z && (eb z =? eb w)%Z.

Lemma eeqb_true_iff : forall z w, eeqb z w = true <-> z = w.
Proof.
  intros [a b] [c d]. unfold eeqb; cbn [ea eb]. split.
  - intro H. apply andb_prop in H. destruct H as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Eis_eq; assumption.
  - intro H. injection H as -> ->. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma eeqb_false_iff : forall z w, eeqb z w = false <-> z <> w.
Proof.
  intros z w. split.
  - intros H Hc. rewrite (proj2 (eeqb_true_iff z w) Hc) in H. discriminate.
  - intro H. destruct (eeqb z w) eqn:E;
      [ exfalso; exact (H (proj1 (eeqb_true_iff z w) E)) | reflexivity ].
Qed.

Definition edvdb (d z : Eis) : bool := eeqb (erem z d) ezero.

Lemma edvdb_true : forall d z, d <> ezero -> edvdb d z = true -> edvd d z.
Proof.
  intros d z Hd H. apply (edvd_rem d z Hd).
  apply eeqb_true_iff. exact H.
Qed.

Lemma edvdb_false : forall d z, d <> ezero -> edvdb d z = false -> ~ edvd d z.
Proof.
  intros d z Hd H Hc. apply (edvd_rem d z Hd) in Hc.
  apply eeqb_false_iff in H. exact (H Hc).
Qed.

Lemma edvdb_of_edvd : forall d z, d <> ezero -> edvd d z -> edvdb d z = true.
Proof.
  intros d z Hd H. destruct (edvdb d z) eqn:E;
    [ reflexivity | exfalso; exact (edvdb_false d z Hd E H) ].
Qed.

Lemma edvdb_of_ndvd : forall d z, d <> ezero -> ~ edvd d z -> edvdb d z = false.
Proof.
  intros d z Hd H. destruct (edvdb d z) eqn:E;
    [ exfalso; exact (H (edvdb_true d z Hd E)) | reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  THE CHARACTER                                                  *)
(* ----------------------------------------------------------------- *)
Definition chiv (p : nat) (pi a : Eis) : Eis :=
  if edvdb pi a then ezero
  else if edvdb pi (esub (epow a ((p - 1) / 3)) eone) then eone
  else if edvdb pi (esub (epow a ((p - 1) / 3)) eom) then eom
  else emul eom eom.

Section Character.

Variable p : nat.
Variable pi : Eis.
Variable t : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdiv : Nat.divide 3 (p - 1)%nat.
Hypothesis Hn : enorm pi = Z.of_nat p.
Hypothesis Ht : edvd pi (esub (eZ t) eom).

Lemma pi_irred : eirred pi.
Proof. exact (norm_prime_eirred pi (Z.of_nat p) Hp Hn). Qed.

Lemma pi_ne0 : pi <> ezero.
Proof. destruct pi_irred as [_ [H _]]. exact H. Qed.

Lemma chiv_zero : forall a, edvd pi a -> chiv p pi a = ezero.
Proof.
  intros a Ha. unfold chiv. rewrite (edvdb_of_edvd pi a pi_ne0 Ha). reflexivity.
Qed.

(* the defining property *)
Theorem chiv_cong : forall a, ~ edvd pi a ->
  econg pi (epow a ((p - 1) / 3)) (chiv p pi a).
Proof.
  intros a Ha.
  pose proof (cubic_symbol p pi t a Hp Hp7 Hdiv Hn Ht Ha) as Hsym.
  cbv zeta in Hsym.
  unfold chiv. rewrite (edvdb_of_ndvd pi a pi_ne0 Ha).
  destruct (edvdb pi (esub (epow a ((p - 1) / 3)) eone)) eqn:E1.
  { exact (edvdb_true _ _ pi_ne0 E1). }
  destruct (edvdb pi (esub (epow a ((p - 1) / 3)) eom)) eqn:E2.
  { exact (edvdb_true _ _ pi_ne0 E2). }
  (* neither 1 nor om, so the trichotomy leaves om^2 *)
  assert (N1 : ~ econg pi (epow a ((p - 1) / 3)) eone)
    by exact (edvdb_false _ _ pi_ne0 E1).
  assert (N2 : ~ econg pi (epow a ((p - 1) / 3)) eom)
    by exact (edvdb_false _ _ pi_ne0 E2).
  destruct Hsym as [[H _] | [[H _] | [H _]]];
    [ exfalso; exact (N1 H) | exfalso; exact (N2 H) | exact H ].
Qed.

Lemma chiv_cuberoot : forall a, ~ edvd pi a -> cuberoot (chiv p pi a).
Proof.
  intros a Ha. unfold chiv, cuberoot.
  rewrite (edvdb_of_ndvd pi a pi_ne0 Ha).
  destruct (edvdb pi (esub (epow a ((p - 1) / 3)) eone));
    [ left; reflexivity | ].
  destruct (edvdb pi (esub (epow a ((p - 1) / 3)) eom));
    [ right; left; reflexivity | right; right; reflexivity ].
Qed.

Lemma chiv_ne0 : forall a, ~ edvd pi a -> chiv p pi a <> ezero.
Proof.
  intros a Ha.
  destruct (chiv_cuberoot a Ha) as [-> | [-> | ->]]; discriminate.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  MULTIPLICATIVITY, with no hypothesis at all                    *)
(* ----------------------------------------------------------------- *)
Theorem chiv_mul : forall a b,
  chiv p pi (emul a b) = emul (chiv p pi a) (chiv p pi b).
Proof.
  intros a b.
  destruct (Eis_dec (erem a pi) ezero) as [Ea | Ea].
  { assert (Ha : edvd pi a) by (apply (edvd_rem pi a pi_ne0); exact Ea).
    rewrite (chiv_zero a Ha).
    rewrite (chiv_zero (emul a b)); [ ring | ].
    destruct Ha as [q Hq]. exists (emul q b). rewrite Hq. ring. }
  destruct (Eis_dec (erem b pi) ezero) as [Eb | Eb].
  { assert (Hb : edvd pi b) by (apply (edvd_rem pi b pi_ne0); exact Eb).
    rewrite (chiv_zero b Hb).
    rewrite (chiv_zero (emul a b)); [ ring | ].
    destruct Hb as [q Hq]. exists (emul q a). rewrite Hq. ring. }
  assert (Ha : ~ edvd pi a) by (intro Hc; apply Ea, (edvd_rem pi a pi_ne0); exact Hc).
  assert (Hb : ~ edvd pi b) by (intro Hc; apply Eb, (edvd_rem pi b pi_ne0); exact Hc).
  assert (Hab : ~ edvd pi (emul a b)) by (apply pi_ndvd_mul; [ apply pi_irred | | ]; assumption).
  assert (Hprod : econg pi (epow (emul a b) ((p - 1) / 3))
                          (emul (chiv p pi a) (chiv p pi b))).
  { rewrite epow_mul_dist. apply econg_mul; [ apply chiv_cong | apply chiv_cong ]; assumption. }
  apply (cuberoot_unique pi (Z.of_nat p) (epow (emul a b) ((p - 1) / 3))).
  - exact Hn.
  - lia.
  - apply chiv_cuberoot; exact Hab.
  - apply cuberoot_mul; apply chiv_cuberoot; assumption.
  - apply chiv_cong; exact Hab.
  - exact Hprod.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the values already known, now as equations                     *)
(* ----------------------------------------------------------------- *)
Lemma pi_ndvd_eone : ~ edvd pi eone.
Proof.
  intro Hc. destruct pi_irred as [Hnu _]. apply Hnu.
  apply (proj1 (edvd_eone pi)). exact Hc.
Qed.

Theorem chiv_one : chiv p pi eone = eone.
Proof.
  apply (cuberoot_unique pi (Z.of_nat p) eone).
  - exact Hn.
  - lia.
  - apply chiv_cuberoot; exact pi_ndvd_eone.
  - left; reflexivity.
  - pose proof (chiv_cong eone pi_ndvd_eone) as H.
    rewrite epow_eone in H. exact H.
  - apply econg_refl.
Qed.

Theorem chiv_omega : chiv p pi eom = epow eom (((p - 1) / 3) mod 3).
Proof.
  apply (cubic_symbol_omega p pi (chiv p pi eom) Hp Hp7 Hn).
  - apply chiv_cuberoot. exact (pi_ndvd_omega pi pi_irred).
  - apply chiv_cong. exact (pi_ndvd_omega pi pi_irred).
Qed.

Theorem chiv_cube : forall beta, ~ edvd pi beta ->
  chiv p pi (epow beta 3) = eone.
Proof.
  intros beta Hb.
  assert (Hcb : ~ edvd pi (epow beta 3)).
  { assert (E : epow beta 3 = emul beta (emul beta beta)) by (cbn [epow]; ring).
    rewrite E.
    apply pi_ndvd_mul; [ apply pi_irred | exact Hb | ].
    apply pi_ndvd_mul; [ apply pi_irred | exact Hb | exact Hb ]. }
  apply (cuberoot_unique pi (Z.of_nat p) (epow (epow beta 3) ((p - 1) / 3))).
  - exact Hn.
  - lia.
  - apply chiv_cuberoot; exact Hcb.
  - left; reflexivity.
  - apply chiv_cong; exact Hcb.
  - exact (cubic_symbol_cube p pi t beta Hp Hp7 Hdiv Hn Ht Hb).
Qed.

End Character.

Print Assumptions edvd_rem.
Print Assumptions chiv_cong.
Print Assumptions chiv_mul.
Print Assumptions chiv_omega.
