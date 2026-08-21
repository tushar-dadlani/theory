(* ================================================================= *)
(*  CEisensteinRelA.v  —  the relation the Gauss sum yields.          *)
(*                                                                    *)
(*    tq_iff       : t q = v mod p has the unique solution v/q         *)
(*    frob_target  : the Frobenius image of g is conj(chi(q)) . g      *)
(*    relation_A   : chi_theta(p J) = conj(chi_pi(q))                  *)
(*                                                                    *)
(*  THIS IS THE WHOLE POINT OF THE CYCLOTOMIC LAYER, discharged in one *)
(*  theorem.  Everything built since CycIndex exists to let g^q be     *)
(*  computed in two different ways and the answers compared:           *)
(*                                                                    *)
(*    upward   g^3 = p J  (E4), so g^{q-1} = (p J)^{(q-1)/3}, a SCALAR *)
(*    sideways g^q = conj(chi_pi(q)) . g  by the Frobenius (E5b)       *)
(*                                                                    *)
(*  Both are statements about g^q; setting them side by side and       *)
(*  cancelling g gives a relation between chi_theta and chi_pi with no *)
(*  Gauss sum left in it.  That is relation (A), and it is the only    *)
(*  place where the two halves of the development meet.                *)
(*                                                                    *)
(*  CANCELLING g IS LEGITIMATE and worth pausing on, because the ring  *)
(*  is NOT known to be a domain -- Phi_p irreducible over Z[om] was    *)
(*  deliberately skipped.  So g is not cancelled as a nonzero element  *)
(*  but multiplied by its explicit inverse: g . g(chibar) = p by       *)
(*  gauss_norm, and p is invertible modulo theta because p and q are   *)
(*  distinct primes.  Everything downstream of that multiplication is  *)
(*  divisibility in Z[om].                                             *)
(*                                                                    *)
(*  THE FROBENIUS IMAGE IS A REINDEXING.  sum_t chi(t) x^{tq} equals   *)
(*  conj(chi(q)) . sum_u chi(u) x^u because t |-> tq permutes Z/p and  *)
(*  chi(u/q) = chi(u) conj(chi(q)).  tq_iff is that permutation,       *)
(*  proved by the same cgp funnel as CycIndex -- both directions are   *)
(*  one linear combination of divisibility witnesses each.             *)
(*                                                                    *)
(*  The character values chi(t)^q are unchanged because q = 1 mod 3,   *)
(*  which is automatic for a norm; that is the fact that made the      *)
(*  Jacobi sum collapse in the first place, and here it is what keeps  *)
(*  the reindexing clean.                                              *)
(*  Axiom-free.                                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Permutation
        Setoid Ring Ring_theory RelationClasses Morphisms.
Require Import ZmodPStar ZmodOrder PrimitiveRoot FpField
        CEisenstein CEisensteinUnits CEisensteinDiv
        CEisensteinGcd CEisensteinSplit CEisensteinUFD CEisensteinResidue
        CEisensteinFermat CEisensteinCubicMul CEisensteinCubicSupp
        CEisensteinCubicFun CEisensteinPrimary CEisensteinSum CEisensteinJacobi
        CEisensteinNormJ CEisensteinJPrimary CEisensteinPiDivJ
        CycIndex CEisensteinCyc CEisensteinCycQuot CEisensteinGaussSum
        CEisensteinBinomial CEisensteinFrobenius CEisensteinQuotCong.
Import ListNotations.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  powers of a cube root                                          *)
(* ----------------------------------------------------------------- *)
Lemma epow_ezero : forall k, (1 <= k)%nat -> epow ezero k = ezero.
Proof. intros k Hk. destruct k as [| k]; [ lia | cbn [epow]; ring ]. Qed.

Lemma cuberoot_cube : forall z, cuberoot z -> epow z 3 = eone.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

Lemma cuberoot_conj' : forall z, cuberoot z -> cuberoot (econj z).
Proof.
  intros z [-> | [-> | ->]]; unfold cuberoot;
    [ left | right; right | right; left ]; reflexivity.
Qed.

Lemma epow_cube_mod3 : forall z, epow z 3 = eone ->
  forall n, epow z n = epow z (n mod 3)%nat.
Proof.
  intros z Hz n.
  assert (E : (n = 3 * (n / 3) + n mod 3)%nat) by apply Nat.div_mod_eq.
  rewrite E at 1. rewrite epow_add, epow_mul, Hz, epow_eone. ring.
Qed.

Lemma cuberoot_pow_1mod3 : forall z k, cuberoot z -> (k mod 3 = 1)%nat ->
  epow z k = z.
Proof.
  intros z k Hz Hk.
  rewrite (epow_cube_mod3 z (cuberoot_cube z Hz) k), Hk.
  cbn [epow]. ring.
Qed.

Section RelA.

Variable p q : nat.
Variable pi theta : Eis.
Variable t0 t1 : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdivp : Nat.divide 3 (p - 1)%nat.
Hypothesis Hnp : enorm pi = Z.of_nat p.
Hypothesis Htp : edvd pi (esub (eZ t0) eom).
Hypothesis Hq : prime (Z.of_nat q).
Hypothesis Hq7 : (7 <= q)%nat.
Hypothesis Hdivq : Nat.divide 3 (q - 1)%nat.
Hypothesis Hnq : enorm theta = Z.of_nat q.
Hypothesis Htq : edvd theta (esub (eZ t1) eom).
Hypothesis Hpq : p <> q.

Notation ch := (chn p pi).
Notation P := (Z.of_nat p).
Notation g := (gs p pi).
Notation gb := (gsb p pi).

Definition Hp1 : (1 <= p)%nat := ltac:(lia).
Definition Hp2 : (2 <= p)%nat := ltac:(lia).

Instance cyc_equiv4 : Equivalence (beq p).
Proof.
  constructor; [ exact (beq_refl p) | exact (beq_sym p) | exact (beq_trans p) ].
Defined.
Instance cadd_Proper4 : Proper (beq p ==> beq p ==> beq p) cadd.
Proof. intros x x' Hx y y' Hy. exact (beq_cadd p x x' y y' Hx Hy). Qed.
Instance cmul_Proper4 : Proper (beq p ==> beq p ==> beq p) (cmul p).
Proof. intros x x' Hx y y' Hy. exact (beq_cmul p Hp1 x x' y y' Hx Hy). Qed.
Instance copp_Proper4 : Proper (beq p ==> beq p) copp.
Proof. intros x x' Hx. exact (beq_copp p x x' Hx). Qed.
Add Ring CycR4 : (cyc_ring p Hp1) (setoid cyc_equiv4 (cyc_ext p Hp1)).

Definition SJ : Eis := emul (eZ P) (Jsum p pi).
Definition mm : nat := ((q - 1) / 3)%nat.
Definition qb : nat := (q mod p)%nat.

Lemma mm_spec : (3 * mm = q - 1)%nat.
Proof.
  destruct Hdivq as [z Hz]. unfold mm.
  rewrite Hz, Nat.div_mul by lia. lia.
Qed.

Lemma theta_irred : eirred theta.
Proof. exact (norm_prime_eirred theta (Z.of_nat q) Hq Hnq). Qed.

Lemma theta_dvd_q : edvd theta (eZ (Z.of_nat q)).
Proof. exact (pi_dvd_p theta (Z.of_nat q) Hnq). Qed.

(* theta divides neither p nor J, because their norms are powers of p *)
Lemma theta_ndvd_of_norm_p : forall z, enorm z = P -> ~ edvd theta z.
Proof.
  intros z Hz Hd.
  assert (Hn : (Z.of_nat q | P)).
  { rewrite <- Hnq, <- Hz. apply edvd_norm. exact Hd. }
  destruct (prime_divisors P Hp (Z.of_nat q) Hn) as [E | [E | [E | E]]];
    try (destruct Hq as [Hq1 _]; lia).
Qed.

Lemma theta_ndvd_p : ~ edvd theta (eZ P).
Proof.
  intro Hd.
  assert (Hn : (Z.of_nat q | enorm (eZ P))).
  { rewrite <- Hnq. apply edvd_norm. exact Hd. }
  assert (E : enorm (eZ P) = P * P) by (unfold enorm, eZ; cbn [ea eb]; ring).
  rewrite E in Hn.
  destruct (prime_mult (Z.of_nat q) Hq P P Hn) as [H | H];
    (destruct (prime_divisors P Hp (Z.of_nat q) H) as [E2 | [E2 | [E2 | E2]]];
     try (destruct Hq as [Hq1 _]; lia); apply Hpq; lia).
Qed.

Lemma theta_ndvd_J : ~ edvd theta (Jsum p pi).
Proof.
  apply theta_ndvd_of_norm_p.
  exact (norm_Jsum p pi t0 Hp Hp7 Hdivp Hnp Htp).
Qed.

Lemma theta_ndvd_SJ : ~ edvd theta SJ.
Proof.
  intro Hd. unfold SJ in Hd.
  destruct (irred_prime theta _ _ theta_irred Hd) as [H | H];
    [ exact (theta_ndvd_p H) | exact (theta_ndvd_J H) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  q is invertible mod p, and the reindexing that follows          *)
(* ----------------------------------------------------------------- *)
Lemma qb_range : (1 <= qb <= p - 1)%nat.
Proof.
  unfold qb.
  assert (Hlt : (q mod p < p)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hne : (q mod p <> 0)%nat).
  { intro Hc. apply Hpq.
    assert (Hd : Nat.divide p q) by (apply Nat.Lcm0.mod_divide; exact Hc).
    destruct (prime_divisors (Z.of_nat q) Hq (Z.of_nat p)
                ltac:(destruct Hd as [c Hc2]; exists (Z.of_nat c); lia))
      as [E | [E | [E | E]]]; try (destruct Hp as [Hp1' _]; lia). }
  lia.
Qed.

Lemma cg_q_qb : (P | Z.of_nat q - Z.of_nat qb).
Proof.
  destruct (cgp_mod p Hp1 q) as [c Hc]. exists (- c). unfold qb. lia.
Qed.

(* the unique t with t q = v mod p *)
Lemma tq_iff : forall t v, (t < p)%nat -> (v < p)%nat ->
  ((t * q) mod p = v)%nat <-> (t = (v * finv p qb) mod p)%nat.
Proof.
  intros t v Ht Hv.
  assert (Hqbr : (1 <= qb <= p - 1)%nat) by exact qb_range.
  pose proof (inv_correct p qb Hp Hqbr) as Hinv.
  assert (Hcinv : (P | Z.of_nat qb * Z.of_nat (finv p qb) - 1)).
  { destruct (cgp_mod p Hp1 (qb * finv p qb)%nat) as [c Hc].
    rewrite Nat2Z.inj_mul in Hc. rewrite Hinv in Hc.
    exists (- c). cbn [Z.of_nat] in Hc. lia. }
  destruct cg_q_qb as [e He].
  destruct Hcinv as [k Hk].
  assert (Q3 : Z.of_nat q = Z.of_nat qb + e * P) by lia.
  assert (Q4 : Z.of_nat qb * Z.of_nat (finv p qb) = 1 + k * P) by lia.
  split.
  - intro Ht2. apply (cgp_eq p Hp1); [ lia | apply Nat.mod_upper_bound; lia | ].
    destruct (cgp_mod p Hp1 (v * finv p qb)%nat) as [c Hc].
    rewrite Nat2Z.inj_mul in Hc.
    destruct (cgp_mod p Hp1 (t * q)%nat) as [d Hd].
    rewrite Nat2Z.inj_mul, Ht2 in Hd.
    assert (Q1 : Z.of_nat ((v * finv p qb) mod p)%nat
                 = Z.of_nat v * Z.of_nat (finv p qb) + c * P) by lia.
    assert (Q2 : Z.of_nat v = Z.of_nat t * Z.of_nat q + d * P) by lia.
    exists (- c - Z.of_nat t * k - Z.of_nat t * e * Z.of_nat (finv p qb)
            - d * Z.of_nat (finv p qb)).
    rewrite Q1, Q2, Q3.
    replace ((Z.of_nat t * (Z.of_nat qb + e * P) + d * P) * Z.of_nat (finv p qb))
      with (Z.of_nat t * (Z.of_nat qb * Z.of_nat (finv p qb))
            + Z.of_nat t * e * P * Z.of_nat (finv p qb)
            + d * P * Z.of_nat (finv p qb)) by ring.
    rewrite Q4. ring.
  - intro Ht2. apply (cgp_eq p Hp1); [ apply Nat.mod_upper_bound; lia | lia | ].
    destruct (cgp_mod p Hp1 (t * q)%nat) as [c Hc]. rewrite Nat2Z.inj_mul in Hc.
    destruct (cgp_mod p Hp1 (v * finv p qb)%nat) as [d Hd].
    rewrite Nat2Z.inj_mul, <- Ht2 in Hd.
    assert (Q1 : Z.of_nat ((t * q) mod p)%nat
                 = Z.of_nat t * Z.of_nat q + c * P) by lia.
    assert (Q2 : Z.of_nat t = Z.of_nat v * Z.of_nat (finv p qb) + d * P) by lia.
    exists (c + Z.of_nat v * k + Z.of_nat v * Z.of_nat (finv p qb) * e
            + d * Z.of_nat q).
    rewrite Q1, Q2, Q3.
    replace ((Z.of_nat v * Z.of_nat (finv p qb) + d * P) * (Z.of_nat qb + e * P))
      with (Z.of_nat v * (Z.of_nat qb * Z.of_nat (finv p qb))
            + Z.of_nat v * Z.of_nat (finv p qb) * e * P
            + d * P * Z.of_nat qb + d * P * (e * P)) by ring.
    rewrite Q4. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the Frobenius image of the Gauss sum                           *)
(* ----------------------------------------------------------------- *)
Lemma q_mod3 : (q mod 3 = 1)%nat.
Proof.
  destruct Hdivq as [z Hz].
  replace q with (1 + z * 3)%nat by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma chn_pow_q : forall t, (t < p)%nat -> epow (ch t) q = ch t.
Proof.
  intros t Ht. destruct (Nat.eq_dec t 0) as [-> | Ht0].
  - rewrite (chn_zero p pi Hp Hnp). apply epow_ezero. lia.
  - apply cuberoot_pow_1mod3; [ | exact q_mod3 ].
    apply (chn_cuberoot p pi Hp Hp7 Hnp). lia.
Qed.

Lemma frob_target : beq p
  (Csum (fun t => cmono p (epow (gs p pi t) q) ((t * q) mod p)%nat) (seq 0 p))
  (cscale (econj (ch qb)) g).
Proof.
  intros v Hv. unfold Csum, cmono, cscale, gs.
  rewrite (Esum_ext _ (fun t => emul (ch t) (cdelta p ((t * q) mod p)%nat v))
             (seq 0 p)).
  2:{ intros t Ht. apply in_seq in Ht.
      rewrite (chn_pow_q t ltac:(lia)). reflexivity. }
  assert (Htv : (((v * finv p qb) mod p)%nat < p)%nat)
    by (apply Nat.mod_upper_bound; lia).
  rewrite (Esum_del (fun t => emul (ch t) (cdelta p ((t * q) mod p)%nat v))
             ((v * finv p qb) mod p)%nat (seq 0 p)
             (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  assert (Hhit : ((((v * finv p qb) mod p) * q) mod p = v)%nat)
    by (apply (tq_iff _ v Htv Hv); reflexivity).
  rewrite Hhit, (cdelta_hit p v).
  assert (Hz : Esum (fun t => emul (ch t) (cdelta p ((t * q) mod p)%nat v))
                 (del ((v * finv p qb) mod p)%nat (seq 0 p)) = ezero).
  { apply Esum_zero_ext. intros t Ht.
    apply In_del in Ht as [Hin Hne]. apply in_seq in Hin.
    assert (Hne2 : (v <> (t * q) mod p)%nat).
    { intro Hc. apply Hne. apply (tq_iff t v ltac:(lia) Hv). symmetry. exact Hc. }
    rewrite (cdelta_miss p Hp1 ((t * q) mod p)%nat v
               ltac:(apply Nat.mod_upper_bound; lia) Hv Hne2). ring. }
  rewrite Hz.
  rewrite (chn_mul p pi t0 Hp Hp7 Hdivp Hnp Htp v (finv p qb)).
  rewrite <- (chn_conj p pi t0 Hp Hp7 Hdivp Hnp Htp qb qb_range).
  ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the chain                                                      *)
(* ----------------------------------------------------------------- *)
Theorem relation_A : chiv q theta SJ = econj (chn p pi q).
Proof.
  (* g^(q-1) is the scalar (p J)^m *)
  assert (HA : ceq p (cpow p g (q - 1)%nat) (cemb p (epow SJ mm))).
  { rewrite <- mm_spec.
    apply (ceq_trans p _ (cpow p (cpow p g 3) mm));
      [ apply beq_ceq, cpow_mul; exact Hp1 | ].
    apply (ceq_trans p _ (cpow p (cemb p SJ) mm)).
    { apply ceq_cpow; [ exact Hp1 | ].
      exact (gauss_cube p pi t0 Hp Hp7 Hdivp Hnp Htp). }
    apply beq_ceq, beq_sym, cemb_pow; exact Hp1. }
  (* hence g^q = g . that scalar *)
  assert (HB : ceq p (cpow p g q) (cmul p g (cemb p (epow SJ mm)))).
  { assert (Hqs : q = S (q - 1)%nat) by lia.
    rewrite Hqs at 1.
    replace (cpow p g (S (q - 1)%nat))
      with (cmul p g (cpow p g (q - 1)%nat)) by reflexivity.
    apply ceq_cmul_r; [ exact Hp1 | exact HA ]. }
  (* and the Frobenius says g^q = conj(chi(q)) g *)
  assert (HC : ccong p (eZ (Z.of_nat q)) (cpow p g q) (cscale (econj (ch qb)) g)).
  { apply (ccong_trans p _ _
             (Csum (fun t => cmono p (epow (gs p pi t) q) ((t * q) mod p)%nat)
                   (seq 0 p)));
      [ exact (frob_pow p Hp1 q Hq g) | ].
    apply ccong_of_beq. exact frob_target. }
  (* put the two together modulo theta *)
  assert (HD : qceq p theta (cmul p g (cemb p (epow SJ mm)))
                            (cscale (econj (ch qb)) g)).
  { apply (qceq_trans p _ _ (cpow p g q)).
    - apply qceq_sym, qceq_of_ceq. exact HB.
    - apply qceq_of_ccong.
      apply (ccong_weaken p (eZ (Z.of_nat q)) theta);
        [ exact theta_dvd_q | exact HC ]. }
  (* multiply by the conjugate Gauss sum; g . gb collapses to p *)
  assert (Hgg : ceq p (cmul p g gb) (cemb p (eZ P))).
  { apply (ceq_trans p _ (csub (cscale (eZ P) (cone p)) cN)).
    - apply beq_ceq. exact (gauss_norm p pi t0 Hp Hp7 Hdivp Hnp Htp).
    - intros u v _ _. unfold csub, cemb, cscale, cN. ring. }
  assert (HE : qceq p theta (cemb p (emul (eZ P) (epow SJ mm)))
                            (cemb p (emul (econj (ch qb)) (eZ P)))).
  { apply (qceq_trans p _ _ (cmul p gb (cmul p g (cemb p (epow SJ mm))))).
    { apply qceq_sym.
      apply (qceq_trans p _ _ (cmul p (cmul p g gb) (cemb p (epow SJ mm))));
        [ apply qceq_of_beq; ring | ].
      apply (qceq_trans p _ _ (cmul p (cemb p (eZ P)) (cemb p (epow SJ mm))));
        [ apply qceq_of_ceq, ceq_cmul_l; [ exact Hp1 | exact Hgg ] | ].
      apply qceq_of_beq, beq_sym, cemb_mul; exact Hp1. }
    apply (qceq_trans p _ _ (cmul p gb (cscale (econj (ch qb)) g)));
      [ apply qceq_cmul_r; [ exact Hp1 | exact HD ] | ].
    apply (qceq_trans p _ _ (cscale (econj (ch qb)) (cmul p gb g))).
    { apply qceq_of_beq. intros u _. unfold cscale, cmul.
      rewrite <- (Esum_scale_l (econj (ch qb))
                    (fun i => emul (gb i) (g (msub p u i))) (seq 0 p)).
      apply Esum_ext. intros i _. ring. }
    apply (qceq_trans p _ _ (cscale (econj (ch qb)) (cmul p g gb))).
    { apply qceq_of_beq, beq_cscale, cmul_comm; exact Hp1. }
    apply (qceq_trans p _ _ (cscale (econj (ch qb)) (cemb p (eZ P)))).
    { apply qceq_of_ceq, ceq_cscale. exact Hgg. }
    apply qceq_of_beq. intros u _. unfold cemb, cscale. ring. }
  (* extract to Z[om] and cancel p *)
  assert (HF : edvd theta (esub (emul (eZ P) (epow SJ mm))
                                (emul (econj (ch qb)) (eZ P))))
    by (apply (qceq_cemb p Hp1 Hp2); exact HE).
  assert (HG : econg theta (epow SJ mm) (econj (ch qb))).
  { destruct HF as [c Hc].
    assert (E : esub (emul (eZ P) (epow SJ mm)) (emul (econj (ch qb)) (eZ P))
                = emul (eZ P) (esub (epow SJ mm) (econj (ch qb)))) by ring.
    rewrite E in Hc.
    destruct (irred_prime theta (eZ P) (esub (epow SJ mm) (econj (ch qb)))
                theta_irred ltac:(exists c; exact Hc)) as [H | H];
      [ exfalso; exact (theta_ndvd_p H) | exact H ]. }
  (* Euler's criterion on the other side, then uniqueness of the cube root *)
  pose proof (chiv_cong q theta t1 Hq Hq7 Hdivq Hnq Htq SJ theta_ndvd_SJ) as HEu.
  assert (Hchq : chn p pi q = ch qb)
    by (unfold qb; symmetry; apply (chiv_mod p pi t0 Hp Hp7 Hdivp Hnp Htp)).
  rewrite Hchq.
  apply (cuberoot_unique theta (Z.of_nat q) (epow SJ mm)).
  - exact Hnq.
  - lia.
  - apply (chiv_cuberoot q theta Hq Hnq). exact theta_ndvd_SJ.
  - apply cuberoot_conj'. apply (chn_cuberoot p pi Hp Hp7 Hnp). exact qb_range.
  - exact HEu.
  - exact HG.
Qed.

End RelA.

Print Assumptions epow_cube_mod3.
Print Assumptions tq_iff.
Print Assumptions frob_target.
Print Assumptions relation_A.
