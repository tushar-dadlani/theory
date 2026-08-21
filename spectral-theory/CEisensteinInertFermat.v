(* ================================================================= *)
(*  CEisensteinInertFermat.v  —  Fermat modulo an INERT prime.        *)
(*                                                                    *)
(*    ebinom       : the binomial theorem in Z[om]                     *)
(*    freshman_eis : (a+b)^q = a^q + b^q  mod q                        *)
(*    Zfermat      : a^q = a  mod q, for every integer a               *)
(*    epow_q_conj  : z^q = conj z  mod q  -- FROBENIUS IS CONJUGATION  *)
(*    inert_fermat : z^{q^2-1} = 1  mod q                              *)
(*                                                                    *)
(*  THE SPLIT CHARACTER LAYER DOES NOT APPLY HERE, and the reason is   *)
(*  structural rather than incidental.  Every lemma about chiv carries *)
(*  the hypothesis pi | t - om for a rational t -- and that hypothesis *)
(*  IS the splitting condition: it says om is congruent to a rational  *)
(*  integer, i.e. that the residue field is F_p rather than F_{p^2}.   *)
(*  For an inert q it is unsatisfiable, since q | t - om would force   *)
(*  q^2 | t^2 + t + 1 and hence 3 | q - 1.  So Fermat, the character,  *)
(*  and everything above them have to be rebuilt for the inert case.   *)
(*                                                                    *)
(*  BUT NOT FROM SCRATCH.  The obvious route -- enumerate the q^2      *)
(*  residues, show multiplication permutes the units, take the product *)
(*  -- is the Z[om] transcription of ZmodPStar.fermat and would run to *)
(*  several hundred lines.  There is a much cheaper one, and it reuses *)
(*  E5a: since q | C(q,k), the freshman's dream holds in Z[om], so     *)
(*                                                                    *)
(*      z^q = a^q + b^q om^q = a + b om^2 = conj z   (mod q)           *)
(*                                                                    *)
(*  using ordinary Fermat on the coefficients and om^q = om^2 because  *)
(*  q = 2 mod 3.  Then z^{q+1} = z conj z = N(z), an ordinary integer, *)
(*  and raising to q-1 gives z^{q^2-1} = N(z)^{q-1} = 1 by Fermat in   *)
(*  Z.  Two applications of a theorem already proved, and no residue   *)
(*  enumeration anywhere.                                              *)
(*                                                                    *)
(*  epow_q_conj IS ALSO THE FACT THE RECIPROCITY ARGUMENT WANTS, not   *)
(*  merely a step towards Fermat: it is what makes chi_q(conj pi) the  *)
(*  conjugate of chi_q(pi), which is what collapses chi_q(p) to 1 in   *)
(*  the inert endgame.  Proving it first is not a detour.              *)
(*                                                                    *)
(*  The binomial theorem here is the Z[om] twin of E5a's, and much     *)
(*  shorter, because Eis has genuine Leibniz equality and a registered *)
(*  ring -- no setoid, no beq, rewrite works everywhere.               *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Ring.
Require Import ZmodPStar BitDensity CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinInert CEisensteinSum CEisensteinNormJ CEisensteinBinomial.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  sums over consecutive runs                                     *)
(* ----------------------------------------------------------------- *)
Lemma econj_invol' : forall z, econj (econj z) = z.
Proof. intros [a b]. unfold econj; cbn [ea eb]. apply Eis_eq; ring. Qed.

Lemma econg_add' : forall d a b c e,
  econg d a b -> econg d c e -> econg d (eadd a c) (eadd b e).
Proof.
  intros d a b c e H1 H2. unfold econg in *.
  assert (E : esub (eadd a c) (eadd b e) = eadd (esub a b) (esub c e)) by ring.
  rewrite E. apply edvd_add; assumption.
Qed.

Lemma Esum_app' : forall f l1 l2,
  Esum f (l1 ++ l2) = eadd (Esum f l1) (Esum f l2).
Proof.
  intros f l1 l2. induction l1 as [| a l1 IH]; [ cbn; unfold Esum; cbn; ring | ].
  cbn [app]. rewrite !Esum_cons, IH. ring.
Qed.

Lemma Esum_seq_cons : forall F m,
  Esum F (seq 0 (S m)) = eadd (F 0%nat) (Esum (fun j => F (S j)) (seq 0 m)).
Proof.
  intros F m. cbn [seq]. rewrite Esum_cons. f_equal.
  unfold Esum. rewrite <- seq_shift, map_map. reflexivity.
Qed.

Lemma Esum_seq_snoc : forall F m,
  Esum F (seq 0 (S m)) = eadd (Esum F (seq 0 m)) (F m).
Proof.
  intros F m. rewrite seq_S, Esum_app', Esum_cons, Esum_nil.
  replace (0 + m)%nat with m by lia. f_equal. ring.
Qed.

Lemma eZ_nat_add : forall a b : nat,
  eZ (Z.of_nat (a + b)%nat) = eadd (eZ (Z.of_nat a)) (eZ (Z.of_nat b)).
Proof. intros a b. rewrite Nat2Z.inj_add, <- eZ_add. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the binomial theorem in Z[om]                                  *)
(* ----------------------------------------------------------------- *)
Definition eterm (a b : Eis) (m k : nat) : Eis :=
  emul (eZ (Z.of_nat (binomial m k))) (emul (epow a k) (epow b (m - k))).

Lemma eterm_zero : forall a b n j, (n < j)%nat -> eterm a b n j = ezero.
Proof.
  intros a b n j Hj. unfold eterm. rewrite (binom_gt n j Hj).
  replace (eZ (Z.of_nat 0)) with ezero by reflexivity. ring.
Qed.

Lemma eterm_first : forall a b n, eterm a b (S n) 0 = emul b (eterm a b n 0).
Proof.
  intros a b n. unfold eterm. rewrite !binom_0_r.
  replace (S n - 0)%nat with (S n) by lia.
  replace (n - 0)%nat with n by lia.
  replace (epow a 0) with eone by reflexivity.
  replace (epow b (S n)) with (emul b (epow b n)) by reflexivity.
  ring.
Qed.

Lemma eterm_split : forall a b n j, (j <= n)%nat ->
  eterm a b (S n) (S j)
  = eadd (emul a (eterm a b n j)) (emul b (eterm a b n (S j))).
Proof.
  intros a b n j Hj. unfold eterm.
  replace (S n - S j)%nat with (n - j)%nat by lia.
  rewrite binom_S, eZ_nat_add.
  destruct (Nat.eq_dec j n) as [-> | Hne].
  - rewrite (binom_gt n (S n) ltac:(lia)).
    replace (eZ (Z.of_nat 0)) with ezero by reflexivity.
    replace (n - n)%nat with 0%nat by lia.
    replace (epow a (S n)) with (emul a (epow a n)) by reflexivity.
    replace (epow b 0) with eone by reflexivity. ring.
  - replace (n - j)%nat with (S (n - S j))%nat by lia.
    replace (epow a (S j)) with (emul a (epow a j)) by reflexivity.
    replace (epow b (S (n - S j))) with (emul b (epow b (n - S j)))
      by reflexivity.
    ring.
Qed.

Theorem ebinom : forall a b n,
  epow (eadd a b) n = Esum (eterm a b n) (seq 0 (S n)).
Proof.
  intros a b n. induction n as [| n IH].
  - cbn [seq]. rewrite Esum_cons, Esum_nil. unfold eterm.
    replace (binomial 0 0) with 1%nat by reflexivity.
    replace (0 - 0)%nat with 0%nat by reflexivity.
    replace (eZ (Z.of_nat 1)) with eone by reflexivity.
    replace (epow a 0) with eone by reflexivity.
    replace (epow b 0) with eone by reflexivity.
    replace (epow (eadd a b) 0) with eone by reflexivity. ring.
  - replace (epow (eadd a b) (S n))
      with (emul (eadd a b) (epow (eadd a b) n)) by reflexivity.
    rewrite IH.
    (* distribute *)
    assert (L : emul (eadd a b) (Esum (eterm a b n) (seq 0 (S n)))
                = eadd (Esum (fun k => emul a (eterm a b n k)) (seq 0 (S n)))
                       (Esum (fun k => emul b (eterm a b n k)) (seq 0 (S n)))).
    { rewrite <- Esum_add, <- Esum_scale_l. apply Esum_ext. intros k _. ring. }
    rewrite L.
    (* and reassemble the other side *)
    rewrite (Esum_seq_cons (eterm a b (S n)) (S n)).
    rewrite (Esum_ext (fun j => eterm a b (S n) (S j))
               (fun j => eadd (emul a (eterm a b n j))
                              (emul b (eterm a b n (S j)))) (seq 0 (S n))).
    2:{ intros j Hj. apply in_seq in Hj. apply eterm_split. lia. }
    rewrite Esum_add, eterm_first.
    rewrite (Esum_seq_snoc (fun j => emul b (eterm a b n (S j))) n).
    rewrite (eterm_zero a b n (S n) ltac:(lia)).
    assert (Hb : Esum (fun k => emul b (eterm a b n k)) (seq 0 (S n))
                 = eadd (emul b (eterm a b n 0%nat))
                        (Esum (fun j => emul b (eterm a b n (S j))) (seq 0 n)))
      by (exact (Esum_seq_cons (fun k => emul b (eterm a b n k)) n)).
    rewrite Hb. ring.
Qed.

Section Inert.

Variable q : nat.
Hypothesis Hq : prime (Z.of_nat q).
Hypothesis Hq2 : (q mod 3 = 2)%nat.
Hypothesis Hq5 : (5 <= q)%nat.

Notation Q := (Z.of_nat q).

Lemma q_irred : eirred (eZ Q).
Proof. exact (eisenstein_inert q Hq Hq2). Qed.

Lemma eZ_dvd_iff : forall m, edvd (eZ Q) (eZ m) <-> (Q | m).
Proof.
  intro m. split.
  - intros [w Hw]. exists (ea w).
    unfold eZ, emul in Hw; cbn [ea eb] in Hw.
    injection Hw as H1 _. lia.
  - intros [c Hc]. exists (eZ c). unfold eZ, emul; cbn [ea eb].
    apply Eis_eq; [ lia | ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the freshman's dream in Z[om]                                  *)
(* ----------------------------------------------------------------- *)
Definition dqe (k : nat) : nat := (binomial q k / q)%nat.

Lemma dqe_spec : forall k, (0 < k < q)%nat -> binomial q k = (q * dqe k)%nat.
Proof.
  intros k Hk. unfold dqe.
  destruct (prime_dvd_binom q Hq k Hk) as [c Hc].
  rewrite Hc, Nat.div_mul by lia. lia.
Qed.

Theorem freshman_eis : forall a b,
  edvd (eZ Q) (esub (epow (eadd a b) q) (eadd (epow a q) (epow b q))).
Proof.
  intros a b.
  assert (Hl : seq 0 (S q) = 0%nat :: seq 1 (q - 1) ++ [q]).
  { cbn [seq]. f_equal. replace q with (S (q - 1)) at 1 by lia.
    rewrite seq_S. repeat f_equal. lia. }
  rewrite ebinom, Hl, Esum_cons, Esum_app', Esum_cons, Esum_nil.
  (* the two ends *)
  assert (H0 : eterm a b q 0 = epow b q).
  { unfold eterm. rewrite binom_0_r.
    replace (q - 0)%nat with q by lia.
    replace (epow a 0) with eone by reflexivity.
    replace (eZ (Z.of_nat 1)) with eone by reflexivity. ring. }
  assert (Hq' : eterm a b q q = epow a q).
  { unfold eterm. rewrite binom_diag.
    replace (q - q)%nat with 0%nat by lia.
    replace (epow b 0) with eone by reflexivity.
    replace (eZ (Z.of_nat 1)) with eone by reflexivity. ring. }
  rewrite H0, Hq'.
  (* the middle is q times something *)
  assert (Hm : Esum (eterm a b q) (seq 1 (q - 1))
               = emul (eZ Q)
                   (Esum (fun k => emul (eZ (Z.of_nat (dqe k)))
                            (emul (epow a k) (epow b (q - k)))) (seq 1 (q - 1)))).
  { rewrite <- Esum_scale_l. apply Esum_ext. intros k Hk. apply in_seq in Hk.
    unfold eterm. rewrite (dqe_spec k ltac:(lia)).
    rewrite Nat2Z.inj_mul, eZ_mul. ring. }
  rewrite Hm.
  exists (Esum (fun k => emul (eZ (Z.of_nat (dqe k)))
                  (emul (epow a k) (epow b (q - k)))) (seq 1 (q - 1))).
  ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  Fermat in Z, and the Frobenius is conjugation                  *)
(* ----------------------------------------------------------------- *)
Lemma Zpow_cong' : forall (x y : Z) (n : nat),
  (Q | x - y) -> (Q | x ^ Z.of_nat n - y ^ Z.of_nat n).
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

Theorem Zfermat : forall a : Z, (Q | a ^ Q - a).
Proof.
  intro a.
  assert (HQ : 2 <= Q) by (destruct Hq; lia).
  set (r := a mod Q).
  assert (Hr : 0 <= r < Q) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Har : (Q | a - r))
    by (exists (a / Q); unfold r; rewrite Z.mod_eq; lia).
  assert (Hpow : (Q | a ^ Q - r ^ Q)).
  { replace Q with (Z.of_nat q) by reflexivity.
    apply Zpow_cong'. exact Har. }
  assert (Hrr : (Q | r ^ Q - r)).
  { destruct (Z.eq_dec r 0) as [-> | Hr0].
    - rewrite Z.pow_0_l by lia. exists 0. ring.
    - set (rn := Z.to_nat r).
      assert (Hrn : Z.of_nat rn = r) by (unfold rn; apply Z2Nat.id; lia).
      assert (Hrange : (1 <= rn <= q - 1)%nat) by lia.
      pose proof (fermat q rn Hq Hrange) as Hf.
      assert (HfZ : (r ^ Z.of_nat (q - 1)%nat) mod Q = 1).
      { apply (f_equal Z.of_nat) in Hf.
        rewrite Nat2Z.inj_mod, Nat2Z.inj_pow, Hrn in Hf. exact Hf. }
      assert (Hd1 : (Q | r ^ Z.of_nat (q - 1)%nat - 1)).
      { apply Z.mod_divide; [ lia | ].
        rewrite Zminus_mod, HfZ, Z.mod_1_l by lia. reflexivity. }
      destruct Hd1 as [c Hc]. exists (c * r).
      assert (E : r ^ Q = r ^ Z.of_nat (q - 1)%nat * r).
      { replace Q with (Z.of_nat (q - 1)%nat + 1) by lia.
        rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. reflexivity. }
      rewrite E.
      assert (E2 : r ^ Z.of_nat (q - 1)%nat * r - r
                   = (r ^ Z.of_nat (q - 1)%nat - 1) * r) by ring.
      rewrite E2, Hc. ring. }
  destruct Hpow as [c Hc]. destruct Hrr as [d Hd]. destruct Har as [e He].
  exists (c + d - e). lia.
Qed.

Lemma eZ_fermat : forall m : Z, econg (eZ Q) (eZ (m ^ Q)) (eZ m).
Proof.
  intro m. unfold econg. rewrite <- eZ_sub.
  apply (proj2 (eZ_dvd_iff (m ^ Q - m))). apply Zfermat.
Qed.

Lemma epow_om_q : epow eom q = emul eom eom.
Proof.
  rewrite (epow_om_mod3 q), Hq2. cbn [epow]. ring.
Qed.

Theorem epow_q_conj : forall z, econg (eZ Q) (epow z q) (econj z).
Proof.
  intro z.
  assert (Hz : z = eadd (eZ (ea z)) (emul (eZ (eb z)) eom)).
  { destruct z as [a b]. unfold eZ, eom, eadd, emul; cbn [ea eb].
    apply Eis_eq; ring. }
  rewrite Hz at 1.
  (* split the power *)
  apply (econg_trans (eZ Q) _
           (eadd (epow (eZ (ea z)) q) (epow (emul (eZ (eb z)) eom) q)) _).
  { destruct (freshman_eis (eZ (ea z)) (emul (eZ (eb z)) eom)) as [w Hw].
    exists w. exact Hw. }
  (* evaluate each piece *)
  rewrite epow_eZ, epow_mul_dist, epow_eZ, epow_om_q.
  apply (econg_trans (eZ Q) _ (eadd (eZ (ea z)) (emul (eZ (eb z)) (emul eom eom))) _).
  { apply econg_add'.
    - replace (Z.of_nat q) with Q by reflexivity. apply eZ_fermat.
    - apply econg_mul; [ | apply econg_refl ].
      replace (Z.of_nat q) with Q by reflexivity. apply eZ_fermat. }
  (* and that is the conjugate *)
  assert (E : eadd (eZ (ea z)) (emul (eZ (eb z)) (emul eom eom)) = econj z).
  { destruct z as [a b]. unfold eZ, eom, eadd, emul, econj; cbn [ea eb].
    apply Eis_eq; ring. }
  rewrite E. apply econg_refl.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  Fermat modulo the inert prime                                  *)
(* ----------------------------------------------------------------- *)
Lemma econj_dvd : forall z, edvd (eZ Q) (econj z) -> edvd (eZ Q) z.
Proof.
  intros z [w Hw]. exists (econj w).
  assert (E : econj (eZ Q) = eZ Q)
    by (unfold eZ, econj; cbn [ea eb]; apply Eis_eq; ring).
  rewrite <- (econj_invol' z), Hw, econj_mul, E. reflexivity.
Qed.

Lemma q_ndvd_norm : forall z, ~ edvd (eZ Q) z -> ~ (Q | enorm z).
Proof.
  intros z Hz Hd.
  assert (Hdd : edvd (eZ Q) (emul z (econj z))).
  { rewrite emul_econj. apply (proj2 (eZ_dvd_iff (enorm z))). exact Hd. }
  destruct (irred_prime (eZ Q) z (econj z) q_irred Hdd) as [H | H];
    [ exact (Hz H) | exact (Hz (econj_dvd z H)) ].
Qed.

Theorem inert_fermat : forall z, ~ edvd (eZ Q) z ->
  econg (eZ Q) (epow z (q * q - 1)%nat) eone.
Proof.
  intros z Hz.
  (* z^(q+1) is the norm *)
  assert (H1 : econg (eZ Q) (epow z (q + 1)%nat) (eZ (enorm z))).
  { replace (epow z (q + 1)%nat) with (emul (epow z q) (epow z 1%nat))
      by (rewrite <- epow_add; f_equal).
    apply (econg_trans (eZ Q) _ (emul (econj z) (epow z 1%nat)) _).
    - apply econg_mul; [ apply epow_q_conj | apply econg_refl ].
    - replace (epow z 1%nat) with z by (cbn [epow]; ring).
      assert (E : emul (econj z) z = eZ (enorm z))
        by (rewrite emul_comm, emul_econj; reflexivity).
      rewrite E. apply econg_refl. }
  (* raise to q-1 *)
  assert (H2 : econg (eZ Q) (epow z ((q + 1) * (q - 1))%nat)
                            (epow (eZ (enorm z)) (q - 1)%nat)).
  { rewrite epow_mul. apply econg_pow. exact H1. }
  replace (q * q - 1)%nat with ((q + 1) * (q - 1))%nat by lia.
  apply (econg_trans (eZ Q) _ (epow (eZ (enorm z)) (q - 1)%nat) _); [ exact H2 | ].
  rewrite epow_eZ.
  (* Fermat in Z on the norm *)
  assert (HQ : 2 <= Q) by (destruct Hq; lia).
  assert (Hnn : ~ (Q | enorm z)) by (apply q_ndvd_norm; exact Hz).
  set (n := enorm z). set (rn := Z.to_nat (n mod Q)).
  assert (Hb : 0 <= n mod Q < Q) by (apply Z.mod_pos_bound; lia).
  assert (Hne : n mod Q <> 0).
  { intro Hc. apply Hnn. apply (proj1 (Z.mod_divide n Q ltac:(lia))). exact Hc. }
  assert (Hrn : Z.of_nat rn = n mod Q) by (unfold rn; apply Z2Nat.id; lia).
  assert (Hrange : (1 <= rn <= q - 1)%nat) by lia.
  pose proof (fermat q rn Hq Hrange) as Hf.
  assert (HfZ : ((n mod Q) ^ Z.of_nat (q - 1)%nat) mod Q = 1).
  { apply (f_equal Z.of_nat) in Hf.
    rewrite Nat2Z.inj_mod, Nat2Z.inj_pow, Hrn in Hf. exact Hf. }
  assert (Hd : (Q | n ^ Z.of_nat (q - 1)%nat - 1)).
  { assert (Hc0 : (Q | n - n mod Q))
      by (exists (n / Q); rewrite Z.mod_eq; lia).
    destruct (Zpow_cong' n (n mod Q) (q - 1)%nat Hc0) as [c Hc].
    assert (Hd1 : (Q | (n mod Q) ^ Z.of_nat (q - 1)%nat - 1)).
    { apply Z.mod_divide; [ lia | ].
      rewrite Zminus_mod, HfZ, Z.mod_1_l by lia. reflexivity. }
    destruct Hd1 as [d Hd1]. exists (c + d). lia. }
  unfold econg. rewrite <- eZ_one, <- eZ_sub.
  apply (proj2 (eZ_dvd_iff _)). exact Hd.
Qed.

End Inert.

Print Assumptions ebinom.
Print Assumptions freshman_eis.
Print Assumptions epow_q_conj.
Print Assumptions inert_fermat.
