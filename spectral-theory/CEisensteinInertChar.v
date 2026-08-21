(* ================================================================= *)
(*  CEisensteinInertChar.v  —  the cubic character mod an inert prime. *)
(*                                                                    *)
(*    chiq a           : the cubic residue symbol modulo q             *)
(*    inert_trichotomy : a^{(q^2-1)/3} hits exactly one cube root      *)
(*    chiq_cong        : the defining congruence                       *)
(*    chiq_mul         : chi(ab) = chi(a) chi(b)                       *)
(*    chiq_conj        : chi(conj a) = conj(chi a)                     *)
(*                                                                    *)
(*  THE DEFINITION IS REUSED VERBATIM.  chiv takes the NORM as its     *)
(*  first argument and is otherwise hypothesis-free, so the inert      *)
(*  character is literally chiv (q*q) (eZ q) -- no new definition, and *)
(*  the same decidable three-way test.  What has to be rebuilt is the  *)
(*  supporting theory, because every existing lemma about chiv assumes *)
(*  the modulus splits.                                                *)
(*                                                                    *)
(*  MOST OF THE THEORY SURVIVES UNCHANGED, and it is worth saying why. *)
(*  cubic_symbol_unique, cuberoot_unique and cube_root_trichotomy were *)
(*  proved from irreducibility and the norm alone -- they never used   *)
(*  the residue field's shape.  So they apply to eZ q with norm q^2    *)
(*  exactly as they applied to a split prime with norm p.  Only the    *)
(*  Fermat input had to be replaced, and that was the previous file.   *)
(*                                                                    *)
(*  chiq_conj IS THE ONE GENUINELY NEW STATEMENT, and it has no        *)
(*  analogue in the split case: there Frobenius is the identity, so    *)
(*  the corresponding fact is vacuous.  Here conj a = a^q, hence       *)
(*  chi(conj a) = chi(a^q) = chi(a)^q = chi(a)^2 = conj(chi a), the    *)
(*  last two steps because q = 2 mod 3 and chi(a) is a cube root.      *)
(*  This is what will collapse chi_q(p) to 1 in the endgame.           *)
(*                                                                    *)
(*  q >= 5 IS REQUIRED, not merely convenient: cubic_symbol_unique     *)
(*  needs norm >= 7, and q = 2 has norm 4.  The excluded case is also  *)
(*  degenerate on its own terms, since (q^2-1)/3 = 1 there.            *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Ring.
Require Import ZmodPStar CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinInert CEisensteinSum CEisensteinJacobi
        CEisensteinNormJ CEisensteinInertFermat.
Import ListNotations.
Open Scope Z_scope.

Lemma econj_sub' : forall x y, econj (esub x y) = esub (econj x) (econj y).
Proof.
  intros [a b] [c d]. unfold econj, esub, eadd, eopp; cbn [ea eb].
  apply Eis_eq; ring.
Qed.

Lemma cuberoot_conj2 : forall z, cuberoot z -> cuberoot (econj z).
Proof.
  intros z [-> | [-> | ->]]; unfold cuberoot;
    [ left | right; right | right; left ]; reflexivity.
Qed.

Section InertChar.

Variable q : nat.
Hypothesis Hq : prime (Z.of_nat q).
Hypothesis Hq2 : (q mod 3 = 2)%nat.
Hypothesis Hq5 : (5 <= q)%nat.

Notation Q := (Z.of_nat q).
Notation QQ := (q * q)%nat.

(* the character, reusing chiv's definition with the norm q^2 *)
Definition chiq (a : Eis) : Eis := chiv QQ (eZ Q) a.

Lemma qq_norm : enorm (eZ Q) = Z.of_nat QQ.
Proof. unfold enorm, eZ; cbn [ea eb]. rewrite Nat2Z.inj_mul. ring. Qed.

Lemma qq_ge7 : (7 <= QQ)%nat. Proof. nia. Qed.

Lemma q_irr : eirred (eZ Q).
Proof. exact (q_irred q Hq Hq2). Qed.

Lemma q_ne0 : eZ Q <> ezero.
Proof. destruct q_irr as [_ [H _]]. exact H. Qed.

Lemma k3 : (((QQ - 1) / 3) * 3 = QQ - 1)%nat.
Proof.
  assert (Hd : Nat.divide 3 (QQ - 1)%nat).
  { assert (Hm : (q = 3 * (q / 3) + 2)%nat)
      by (pose proof (Nat.div_mod_eq q 3); lia).
    exists (3 * (q / 3) * (q / 3) + 4 * (q / 3) + 1)%nat. nia. }
  destruct Hd as [z Hz]. rewrite Hz, Nat.div_mul by lia. lia.
Qed.

Lemma econg_conj : forall x y, econg (eZ Q) x y -> econg (eZ Q) (econj x) (econj y).
Proof.
  intros x y [w Hw]. exists (econj w). unfold econg in *.
  assert (E : econj (eZ Q) = eZ Q)
    by (unfold eZ, econj; cbn [ea eb]; apply Eis_eq; ring).
  rewrite <- econj_sub', Hw, econj_mul, E. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the trichotomy                                                 *)
(* ----------------------------------------------------------------- *)
Theorem inert_trichotomy : forall a, ~ edvd (eZ Q) a ->
  let x := epow a ((QQ - 1) / 3)%nat in
  (econg (eZ Q) x eone /\ ~ econg (eZ Q) x eom /\ ~ econg (eZ Q) x (emul eom eom))
  \/ (econg (eZ Q) x eom /\ ~ econg (eZ Q) x eone /\ ~ econg (eZ Q) x (emul eom eom))
  \/ (econg (eZ Q) x (emul eom eom) /\ ~ econg (eZ Q) x eone /\ ~ econg (eZ Q) x eom).
Proof.
  intros a Ha x.
  assert (Hcube : econg (eZ Q) (epow x 3) eone).
  { unfold x. rewrite <- epow_mul, k3.
    exact (inert_fermat q Hq Hq2 Hq5 a Ha). }
  apply (cubic_symbol_unique (eZ Q) (Z.of_nat QQ) x q_irr qq_norm
           ltac:(pose proof qq_ge7; lia) Hcube).
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the character's defining property                              *)
(* ----------------------------------------------------------------- *)
Theorem chiq_cong : forall a, ~ edvd (eZ Q) a ->
  econg (eZ Q) (epow a ((QQ - 1) / 3)%nat) (chiq a).
Proof.
  intros a Ha.
  pose proof (inert_trichotomy a Ha) as Hsym. cbv zeta in Hsym.
  unfold chiq, chiv. rewrite (edvdb_of_ndvd (eZ Q) a q_ne0 Ha).
  destruct (edvdb (eZ Q) (esub (epow a ((QQ - 1) / 3)%nat) eone)) eqn:E1.
  { exact (edvdb_true _ _ q_ne0 E1). }
  destruct (edvdb (eZ Q) (esub (epow a ((QQ - 1) / 3)%nat) eom)) eqn:E2.
  { exact (edvdb_true _ _ q_ne0 E2). }
  assert (N1 : ~ econg (eZ Q) (epow a ((QQ - 1) / 3)%nat) eone)
    by exact (edvdb_false _ _ q_ne0 E1).
  assert (N2 : ~ econg (eZ Q) (epow a ((QQ - 1) / 3)%nat) eom)
    by exact (edvdb_false _ _ q_ne0 E2).
  destruct Hsym as [[H _] | [[H _] | [H _]]];
    [ exfalso; exact (N1 H) | exfalso; exact (N2 H) | exact H ].
Qed.

Lemma chiq_zero : forall a, edvd (eZ Q) a -> chiq a = ezero.
Proof.
  intros a Ha. unfold chiq, chiv.
  rewrite (edvdb_of_edvd (eZ Q) a q_ne0 Ha). reflexivity.
Qed.

Lemma chiq_cuberoot : forall a, ~ edvd (eZ Q) a -> cuberoot (chiq a).
Proof.
  intros a Ha. unfold chiq, chiv, cuberoot.
  rewrite (edvdb_of_ndvd (eZ Q) a q_ne0 Ha).
  destruct (edvdb (eZ Q) (esub (epow a ((QQ - 1) / 3)%nat) eone));
    [ left; reflexivity | ].
  destruct (edvdb (eZ Q) (esub (epow a ((QQ - 1) / 3)%nat) eom));
    [ right; left; reflexivity | right; right; reflexivity ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  multiplicativity                                               *)
(* ----------------------------------------------------------------- *)
Theorem chiq_mul : forall a b, chiq (emul a b) = emul (chiq a) (chiq b).
Proof.
  intros a b.
  destruct (Eis_dec (erem a (eZ Q)) ezero) as [Ea | Ea].
  { assert (Ha : edvd (eZ Q) a) by (apply (edvd_rem (eZ Q) a q_ne0); exact Ea).
    rewrite (chiq_zero a Ha), (chiq_zero (emul a b)); [ ring | ].
    destruct Ha as [w Hw]. exists (emul w b). rewrite Hw. ring. }
  destruct (Eis_dec (erem b (eZ Q)) ezero) as [Eb | Eb].
  { assert (Hb : edvd (eZ Q) b) by (apply (edvd_rem (eZ Q) b q_ne0); exact Eb).
    rewrite (chiq_zero b Hb), (chiq_zero (emul a b)); [ ring | ].
    destruct Hb as [w Hw]. exists (emul w a). rewrite Hw. ring. }
  assert (Ha : ~ edvd (eZ Q) a)
    by (intro Hc; apply Ea, (edvd_rem (eZ Q) a q_ne0); exact Hc).
  assert (Hb : ~ edvd (eZ Q) b)
    by (intro Hc; apply Eb, (edvd_rem (eZ Q) b q_ne0); exact Hc).
  assert (Hab : ~ edvd (eZ Q) (emul a b))
    by (apply pi_ndvd_mul; [ apply q_irr | | ]; assumption).
  apply (cuberoot_unique (eZ Q) (Z.of_nat QQ)
           (epow (emul a b) ((QQ - 1) / 3)%nat)).
  - exact qq_norm.
  - pose proof qq_ge7; lia.
  - apply chiq_cuberoot; exact Hab.
  - apply cuberoot_mul; apply chiq_cuberoot; assumption.
  - apply chiq_cong; exact Hab.
  - rewrite epow_mul_dist. apply econg_mul; apply chiq_cong; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the character commutes with conjugation                        *)
(* ----------------------------------------------------------------- *)
Theorem chiq_conj : forall a, ~ edvd (eZ Q) a ->
  chiq (econj a) = econj (chiq a).
Proof.
  intros a Ha.
  assert (Hca : ~ edvd (eZ Q) (econj a))
    by (intro Hc; apply Ha; apply (econj_dvd q a); exact Hc).
  apply (cuberoot_unique (eZ Q) (Z.of_nat QQ)
           (epow (econj a) ((QQ - 1) / 3)%nat)).
  - exact qq_norm.
  - pose proof qq_ge7; lia.
  - apply chiq_cuberoot; exact Hca.
  - apply cuberoot_conj2, chiq_cuberoot; exact Ha.
  - apply chiq_cong; exact Hca.
  - (* conj(a)^k = (a^k)^q = conj(a^k) = conj(chi(a)) *)
    apply (econg_trans (eZ Q) _ (epow (epow a q) ((QQ - 1) / 3)%nat) _).
    { apply econg_pow. apply econg_sym. exact (epow_q_conj q Hq Hq2 Hq5 a). }
    rewrite <- epow_mul.
    apply (econg_trans (eZ Q) _ (econj (epow a ((QQ - 1) / 3)%nat)) _).
    { replace (q * ((QQ - 1) / 3))%nat with (((QQ - 1) / 3) * q)%nat by lia.
      rewrite epow_mul.
      exact (epow_q_conj q Hq Hq2 Hq5 (epow a ((QQ - 1) / 3)%nat)). }
    apply econg_conj. apply chiq_cong. exact Ha.
Qed.

End InertChar.

Print Assumptions inert_trichotomy.
Print Assumptions chiq_cong.
Print Assumptions chiq_mul.
Print Assumptions chiq_conj.
