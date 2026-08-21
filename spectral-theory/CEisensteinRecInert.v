(* ================================================================= *)
(*  CEisensteinRecInert.v  —  cubic reciprocity, INERT case.          *)
(*                                                                    *)
(*    tqi_iff                 : t q = v mod p, uniquely solvable       *)
(*    frob_g, frob_gb         : the Frobenius swaps g and g(chibar)    *)
(*    frob_twice              : g^{q^2} = chi_pi(q) . g                *)
(*    relation_A_inert        : chi_q(p J) = chi_pi(q)                 *)
(*    cubic_reciprocity_inert : chi_q(pi) = chi_pi(q)                  *)
(*                                                                    *)
(*  THE FROBENIUS HAS TO BE APPLIED TWICE, and the intermediate step   *)
(*  is the interesting one.  For a SPLIT theta the norm is q and one   *)
(*  application suffices, landing back on g.  Here the norm is q^2,    *)
(*  and one application does NOT land on g: since q = 2 mod 3 the      *)
(*  character values get conjugated, so                                *)
(*                                                                    *)
(*      g^q = chi_pi(q) . g(chibar)                                    *)
(*                                                                    *)
(*  -- the Gauss sum is sent to the CONJUGATE Gauss sum.  Applying it  *)
(*  again sends g(chibar) back to g, and the two scalars multiply to   *)
(*  chi_pi(q).  So the pair (g, g(chibar)) is what the Frobenius acts  *)
(*  on, and only the square of it fixes each.                          *)
(*                                                                    *)
(*  THE ENDGAME IS SHORTER THAN THE SPLIT ONE.  There, relation (A)    *)
(*  had to be combined with its mirror image.  Here chi_q(p) collapses *)
(*  on its own: p = pi conj(pi), and chiq_conj says                    *)
(*  chi_q(conj pi) = conj(chi_q(pi)), so                               *)
(*  chi_q(p) = chi_q(pi) conj(chi_q(pi)) = 1, and relation (A) reads   *)
(*  chi_q(pi) = chi_pi(q) directly.  No mirror run is needed, because  *)
(*  the inert prime's own Frobenius supplies the second relation.      *)
(*                                                                    *)
(*  tq_iff HAD TO BE RE-PROVED with 5 <= q in place of 7 <= q: the     *)
(*  inert primes congruent to 2 mod 3 start at 5, and the split-case   *)
(*  version had 7 <= q baked in from a lia that happened to consume    *)
(*  it.  Excluding q = 5 would have been a silent narrowing of the     *)
(*  theorem, so the forty lines are worth it.                          *)
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
        CEisensteinInert CEisensteinInertFermat CEisensteinInertChar
        CycIndex CEisensteinCyc CEisensteinCycQuot CEisensteinGaussSum
        CEisensteinBinomial CEisensteinFrobenius CEisensteinQuotCong
        CEisensteinRelA CEisensteinReciprocity.
Import ListNotations.
Open Scope Z_scope.

Lemma Csum_ext_pt : forall (F G : nat -> Cyc) (v : nat) (l : list nat),
  (forall k, In k l -> F k v = G k v) -> Csum F l v = Csum G l v.
Proof. intros F G v l H. unfold Csum. apply Esum_ext. exact H. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  cube roots raised to the q-th power, q = 2 mod 3               *)
(* ----------------------------------------------------------------- *)
Lemma cuberoot_pow_2mod3 : forall z k, cuberoot z -> (k mod 3 = 2)%nat ->
  epow z k = econj z.
Proof.
  intros z k Hz Hk.
  rewrite (epow_cube_mod3 z (cuberoot_cube z Hz) k), Hk.
  destruct Hz as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma cuberoot_collapse : forall z, cuberoot z ->
  emul (emul z z) (econj z) = z.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  congruence of group-ring elements under products and powers    *)
(* ----------------------------------------------------------------- *)
Lemma ccong_cmul : forall p d f f' g g', (1 <= p)%nat ->
  ccong p d f f' -> ccong p d g g' ->
  ccong p d (cmul p f g) (cmul p f' g').
Proof.
  intros p d f f' g g' Hp1 H1 H2 n _. unfold cmul.
  rewrite <- Esum_sub.
  apply Esum_dvd. intros i Hi. apply in_seq in Hi.
  destruct (H1 i ltac:(lia)) as [x Hx].
  destruct (H2 (msub p n i) ltac:(apply msub_lt; exact Hp1)) as [y Hy].
  exists (eadd (emul x (g (msub p n i))) (emul (f' i) y)).
  assert (E : esub (emul (f i) (g (msub p n i))) (emul (f' i) (g' (msub p n i)))
              = eadd (emul (esub (f i) (f' i)) (g (msub p n i)))
                     (emul (f' i) (esub (g (msub p n i)) (g' (msub p n i)))))
    by ring.
  rewrite E, Hx, Hy. ring.
Qed.

Lemma ccong_cpow : forall p d f f' k, (1 <= p)%nat ->
  ccong p d f f' -> ccong p d (cpow p f k) (cpow p f' k).
Proof.
  intros p d f f' k Hp1 H. induction k as [| k IH]; cbn [cpow].
  - apply ccong_refl.
  - apply ccong_cmul; assumption.
Qed.

Lemma cscale_cpow : forall p c f k, (1 <= p)%nat ->
  beq p (cpow p (cscale c f) k) (cscale (epow c k) (cpow p f k)).
Proof.
  intros p c f k Hp1. induction k as [| k IH].
  - cbn [cpow epow]. intros u _. unfold cscale, cone. ring.
  - replace (cpow p (cscale c f) (S k))
      with (cmul p (cscale c f) (cpow p (cscale c f) k)) by reflexivity.
    apply (beq_trans p _ (cmul p (cscale c f) (cscale (epow c k) (cpow p f k))));
      [ exact (beq_cmul p Hp1 _ _ _ _ (beq_refl p _) IH) | ].
    intros n _. unfold cmul, cscale.
    replace (epow c (S k)) with (emul c (epow c k)) by reflexivity.
    replace (cpow p f (S k)) with (cmul p f (cpow p f k)) by reflexivity.
    unfold cmul. rewrite <- Esum_scale_l.
    apply Esum_ext. intros i _. ring.
Qed.

Section RecInert.

Variable p q : nat.
Variable pi : Eis.
Variable t0 : Z.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hp7 : (7 <= p)%nat.
Hypothesis Hdivp : Nat.divide 3 (p - 1)%nat.
Hypothesis Hnp : enorm pi = Z.of_nat p.
Hypothesis Htp : edvd pi (esub (eZ t0) eom).
Hypothesis Hprp : primary pi.
Hypothesis Hq : prime (Z.of_nat q).
Hypothesis Hq2 : (q mod 3 = 2)%nat.
Hypothesis Hq5 : (5 <= q)%nat.

Notation ch := (chn p pi).
Notation P := (Z.of_nat p).
Notation Q := (Z.of_nat q).
Notation g := (gs p pi).
Notation gb := (gsb p pi).

Definition Hp1' : (1 <= p)%nat := ltac:(lia).
Definition Hp2' : (2 <= p)%nat := ltac:(lia).

Instance cyc_equiv5 : Equivalence (beq p).
Proof.
  constructor; [ exact (beq_refl p) | exact (beq_sym p) | exact (beq_trans p) ].
Defined.
Instance cadd_Proper5 : Proper (beq p ==> beq p ==> beq p) cadd.
Proof. intros x x' Hx y y' Hy. exact (beq_cadd p x x' y y' Hx Hy). Qed.
Instance cmul_Proper5 : Proper (beq p ==> beq p ==> beq p) (cmul p).
Proof. intros x x' Hx y y' Hy. exact (beq_cmul p Hp1' x x' y y' Hx Hy). Qed.
Instance copp_Proper5 : Proper (beq p ==> beq p) copp.
Proof. intros x x' Hx. exact (beq_copp p x x' Hx). Qed.
Add Ring CycR5 : (cyc_ring p Hp1') (setoid cyc_equiv5 (cyc_ext p Hp1')).

Lemma Hpq : p <> q.
Proof.
  intro Hc. assert (Hm : (p mod 3 = 2)%nat) by (rewrite Hc; exact Hq2).
  destruct Hdivp as [z Hz].
  assert (Hd : (p = 3 * (p / 3) + 2)%nat)
    by (pose proof (Nat.div_mod_eq p 3); lia).
  lia.
Qed.

Notation QQ := (q * q)%nat.
Definition SJ' : Eis := emul (eZ P) (Jsum p pi).
Definition mmi : nat := ((QQ - 1) / 3)%nat.
Definition qbi : nat := (q mod p)%nat.

Lemma qq_norm' : enorm (eZ Q) = Z.of_nat QQ.
Proof. unfold enorm, eZ; cbn [ea eb]. rewrite Nat2Z.inj_mul. ring. Qed.

Lemma mmi_spec : (3 * mmi = QQ - 1)%nat.
Proof.
  assert (Hd : Nat.divide 3 (QQ - 1)%nat).
  { assert (Hm : exists m, (q = 3 * m + 2)%nat)
      by (exists (q / 3)%nat; pose proof (Nat.div_mod_eq q 3); lia).
    destruct Hm as [m Hm].
    exists (3 * m * m + 4 * m + 1)%nat. rewrite Hm. nia. }
  destruct Hd as [z Hz]. unfold mmi. rewrite Hz, Nat.div_mul by lia. lia.
Qed.

Lemma qq_ndvd_prime : forall (r : nat) (z : Eis), prime (Z.of_nat r) ->
  enorm z = Z.of_nat r -> ~ edvd (eZ Q) z.
Proof.
  intros r z Hr Hz Hd.
  assert (Hn : (Z.of_nat QQ | Z.of_nat r))
    by (rewrite <- qq_norm', <- Hz; apply edvd_norm; exact Hd).
  assert (HQQ : 25 <= Z.of_nat QQ) by nia.
  destruct (prime_divisors (Z.of_nat r) Hr (Z.of_nat QQ) Hn)
    as [E | [E | [E | E]]]; try (destruct Hr as [Hr1 _]; lia).
  (* r = q^2, so q divides the prime r strictly between 1 and r *)
  assert (Hqd : (Q | Z.of_nat r)) by (exists Q; rewrite <- E, Nat2Z.inj_mul; ring).
  destruct (prime_divisors (Z.of_nat r) Hr Q Hqd)
    as [E2 | [E2 | [E2 | E2]]]; try lia.
  rewrite <- E2 in E. nia.
Qed.

Lemma theta_ndvd_p_i : ~ edvd (eZ Q) (eZ P).
Proof.
  intro Hd.
  assert (HQP : (Q | P)) by (apply (eZ_dvd_iff q Hq2 Hq5); exact Hd).
  destruct (prime_divisors P Hp Q HQP) as [E | [E | [E | E]]];
    try (destruct Hp as [Hp1'' _]; lia).
  (* Q = P, but then p = q, contradicting the residues mod 3 *)
  assert (Hc : p = q) by lia. apply Hpq. exact Hc.
Qed.

Lemma theta_ndvd_pi : ~ edvd (eZ Q) pi.
Proof. apply (qq_ndvd_prime p pi Hp Hnp). Qed.

Lemma theta_ndvd_J_i : ~ edvd (eZ Q) (Jsum p pi).
Proof.
  apply (qq_ndvd_prime p (Jsum p pi) Hp).
  exact (norm_Jsum p pi t0 Hp Hp7 Hdivp Hnp Htp).
Qed.

Lemma theta_ndvd_SJ_i : ~ edvd (eZ Q) SJ'.
Proof.
  intro Hd. unfold SJ' in Hd.
  destruct (irred_prime (eZ Q) _ _ (q_irred q Hq Hq2) Hd) as [H | H];
    [ exact (theta_ndvd_p_i H) | exact (theta_ndvd_J_i H) ].
Qed.

Lemma qbi_range : (1 <= qbi <= p - 1)%nat.
Proof.
  unfold qbi.
  assert (Hlt : (q mod p < p)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hne : (q mod p <> 0)%nat).
  { intro Hc. apply Hpq.
    assert (Hd : Nat.divide p q) by (apply Nat.Lcm0.mod_divide; exact Hc).
    destruct (prime_divisors (Z.of_nat q) Hq (Z.of_nat p)
                ltac:(destruct Hd as [c Hc2]; exists (Z.of_nat c); lia))
      as [E | [E | [E | E]]]; try (destruct Hp as [Hp1'' _]; lia). }
  lia.
Qed.

(* the analogue of tq_iff, but for q >= 5 rather than q >= 7,
   since the inert primes start at 5 *)
Lemma cg_q_qbi : (P | Q - Z.of_nat qbi).
Proof.
  destruct (cgp_mod p Hp1' q) as [c Hc]. exists (- c). unfold qbi. lia.
Qed.

Lemma tqi_iff : forall t v, (t < p)%nat -> (v < p)%nat ->
  ((t * q) mod p = v)%nat <-> (t = (v * finv p qbi) mod p)%nat.
Proof.
  intros t v Ht Hv.
  pose proof (inv_correct p qbi Hp qbi_range) as Hinv.
  assert (Hcinv : (P | Z.of_nat qbi * Z.of_nat (finv p qbi) - 1)).
  { destruct (cgp_mod p Hp1' (qbi * finv p qbi)%nat) as [c Hc].
    rewrite Nat2Z.inj_mul, Hinv in Hc.
    exists (- c). cbn [Z.of_nat] in Hc. lia. }
  destruct cg_q_qbi as [e He]. destruct Hcinv as [k Hk].
  assert (Q3 : Q = Z.of_nat qbi + e * P) by lia.
  assert (Q4 : Z.of_nat qbi * Z.of_nat (finv p qbi) = 1 + k * P) by lia.
  split.
  - intro Ht2. apply (cgp_eq p Hp1'); [ lia | apply Nat.mod_upper_bound; lia | ].
    destruct (cgp_mod p Hp1' (v * finv p qbi)%nat) as [c Hc].
    rewrite Nat2Z.inj_mul in Hc.
    destruct (cgp_mod p Hp1' (t * q)%nat) as [d Hd].
    rewrite Nat2Z.inj_mul, Ht2 in Hd.
    assert (Q1 : Z.of_nat ((v * finv p qbi) mod p)%nat
                 = Z.of_nat v * Z.of_nat (finv p qbi) + c * P) by lia.
    assert (Q2 : Z.of_nat v = Z.of_nat t * Q + d * P) by lia.
    exists (- c - Z.of_nat t * k - Z.of_nat t * e * Z.of_nat (finv p qbi)
            - d * Z.of_nat (finv p qbi)).
    rewrite Q1, Q2, Q3.
    replace ((Z.of_nat t * (Z.of_nat qbi + e * P) + d * P) * Z.of_nat (finv p qbi))
      with (Z.of_nat t * (Z.of_nat qbi * Z.of_nat (finv p qbi))
            + Z.of_nat t * e * P * Z.of_nat (finv p qbi)
            + d * P * Z.of_nat (finv p qbi)) by ring.
    rewrite Q4. ring.
  - intro Ht2. apply (cgp_eq p Hp1'); [ apply Nat.mod_upper_bound; lia | lia | ].
    destruct (cgp_mod p Hp1' (t * q)%nat) as [c Hc]. rewrite Nat2Z.inj_mul in Hc.
    destruct (cgp_mod p Hp1' (v * finv p qbi)%nat) as [d Hd].
    rewrite Nat2Z.inj_mul, <- Ht2 in Hd.
    assert (Q1 : Z.of_nat ((t * q) mod p)%nat = Z.of_nat t * Q + c * P) by lia.
    assert (Q2 : Z.of_nat t = Z.of_nat v * Z.of_nat (finv p qbi) + d * P) by lia.
    exists (c + Z.of_nat v * k + Z.of_nat v * Z.of_nat (finv p qbi) * e
            + d * Q).
    rewrite Q1, Q2, Q3.
    replace ((Z.of_nat v * Z.of_nat (finv p qbi) + d * P)
             * (Z.of_nat qbi + e * P))
      with (Z.of_nat v * (Z.of_nat qbi * Z.of_nat (finv p qbi))
            + Z.of_nat v * Z.of_nat (finv p qbi) * e * P
            + d * P * Z.of_nat qbi + d * P * (e * P)) by ring.
    rewrite Q4. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the Frobenius image, twice                                     *)
(* ----------------------------------------------------------------- *)
Lemma reindex_mono : forall (h : nat -> Eis) (v : nat), (v < p)%nat ->
  Csum (fun t => cmono p (h t) ((t * q) mod p)%nat) (seq 0 p) v
  = h ((v * finv p qbi) mod p)%nat.
Proof.
  intros h v Hv. unfold Csum, cmono, cscale.
  assert (Htv : (((v * finv p qbi) mod p)%nat < p)%nat)
    by (apply Nat.mod_upper_bound; lia).
  rewrite (Esum_del (fun t => emul (h t) (cdelta p ((t * q) mod p)%nat v))
             ((v * finv p qbi) mod p)%nat (seq 0 p)
             (seq_NoDup _ _) ltac:(apply in_seq; lia)).
  assert (Hhit : ((((v * finv p qbi) mod p) * q) mod p = v)%nat)
    by (apply (tqi_iff _ v Htv Hv); reflexivity).
  rewrite Hhit, (cdelta_hit p v).
  assert (Hz : Esum (fun t => emul (h t) (cdelta p ((t * q) mod p)%nat v))
                 (del ((v * finv p qbi) mod p)%nat (seq 0 p)) = ezero).
  { apply Esum_zero_ext. intros t Ht.
    apply In_del in Ht as [Hin Hne]. apply in_seq in Hin.
    assert (Hne2 : (v <> (t * q) mod p)%nat).
    { intro Hc. apply Hne.
      apply (tqi_iff t v ltac:(lia) Hv). symmetry. exact Hc. }
    rewrite (cdelta_miss p Hp1' ((t * q) mod p)%nat v
               ltac:(apply Nat.mod_upper_bound; lia) Hv Hne2). ring. }
  rewrite Hz. ring.
Qed.

Lemma chn_pow_q_inert : forall t, (t < p)%nat -> epow (ch t) q = econj (ch t).
Proof.
  intros t Ht. destruct (Nat.eq_dec t 0) as [-> | Ht0].
  - rewrite (chn_zero p pi Hp Hnp).
    rewrite (epow_ezero q ltac:(lia)). reflexivity.
  - apply cuberoot_pow_2mod3; [ | exact Hq2 ].
    apply (chn_cuberoot p pi Hp Hp7 Hnp). lia.
Qed.

Lemma gb_pow_q_inert : forall t, (t < p)%nat -> epow (gsb p pi t) q = ch t.
Proof.
  intros t Ht. unfold gsb, cbar, gs.
  destruct (Nat.eq_dec t 0) as [-> | Ht0].
  - rewrite (chn_zero p pi Hp Hnp), econj_zero.
    rewrite (epow_ezero q ltac:(lia)). reflexivity.
  - rewrite cuberoot_pow_2mod3;
      [ apply econj_invol
      | apply cuberoot_conj2, (chn_cuberoot p pi Hp Hp7 Hnp); lia
      | exact Hq2 ].
Qed.

Lemma frob_g : beq p
  (Csum (fun t => cmono p (epow (gs p pi t) q) ((t * q) mod p)%nat) (seq 0 p))
  (cscale (ch qbi) gb).
Proof.
  intros v Hv.
  rewrite (Csum_ext_pt (fun t => cmono p (epow (gs p pi t) q) ((t * q) mod p)%nat)
             (fun t => cmono p (gsb p pi t) ((t * q) mod p)%nat) v).
  2:{ intros t Ht. apply in_seq in Ht. unfold gsb, cbar, gs.
      rewrite (chn_pow_q_inert t ltac:(lia)). reflexivity. }
  rewrite (reindex_mono (gsb p pi) v Hv).
  unfold gsb, cbar, gs, cscale.
  rewrite (chn_mul p pi t0 Hp Hp7 Hdivp Hnp Htp v (finv p qbi)).
  rewrite <- (chn_conj p pi t0 Hp Hp7 Hdivp Hnp Htp qbi qbi_range).
  rewrite econj_mul, econj_invol. ring.
Qed.

Lemma frob_gb : beq p
  (Csum (fun t => cmono p (epow (gsb p pi t) q) ((t * q) mod p)%nat) (seq 0 p))
  (cscale (econj (ch qbi)) g).
Proof.
  intros v Hv.
  rewrite (Csum_ext_pt (fun t => cmono p (epow (gsb p pi t) q) ((t * q) mod p)%nat)
             (fun t => cmono p (chn p pi t) ((t * q) mod p)%nat) v).
  2:{ intros t Ht. apply in_seq in Ht.
      rewrite (gb_pow_q_inert t ltac:(lia)). reflexivity. }
  rewrite (reindex_mono (chn p pi) v Hv).
  unfold gs, cscale.
  rewrite (chn_mul p pi t0 Hp Hp7 Hdivp Hnp Htp v (finv p qbi)).
  rewrite <- (chn_conj p pi t0 Hp Hp7 Hdivp Hnp Htp qbi qbi_range). ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the Frobenius, applied twice                                   *)
(* ----------------------------------------------------------------- *)
Lemma ccong_cscale : forall d c f f', ccong p d f f' ->
  ccong p d (cscale c f) (cscale c f').
Proof.
  intros d c f f' H u Hu. destruct (H u Hu) as [w Hw].
  exists (emul c w). unfold cscale.
  assert (E : esub (emul c (f u)) (emul c (f' u)) = emul c (esub (f u) (f' u)))
    by ring.
  rewrite E, Hw. ring.
Qed.

Lemma cuberoot_conj_sq : forall z, cuberoot z -> emul (econj z) (econj z) = z.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

Lemma frob_twice : ccong p (eZ Q) (cpow p g QQ) (cscale (ch qbi) g).
Proof.
  assert (Hg : ccong p (eZ Q) (cpow p g q) (cscale (ch qbi) gb)).
  { apply (ccong_trans p _ _
             (Csum (fun t => cmono p (epow (gs p pi t) q) ((t * q) mod p)%nat)
                   (seq 0 p)));
      [ exact (frob_pow p Hp1' q Hq g) | apply ccong_of_beq, frob_g ]. }
  assert (Hgb : ccong p (eZ Q) (cpow p gb q) (cscale (econj (ch qbi)) g)).
  { apply (ccong_trans p _ _
             (Csum (fun t => cmono p (epow (gsb p pi t) q) ((t * q) mod p)%nat)
                   (seq 0 p)));
      [ exact (frob_pow p Hp1' q Hq gb) | apply ccong_of_beq, frob_gb ]. }
  (* raise the first to the q-th power *)
  assert (H2 : ccong p (eZ Q) (cpow p (cpow p g q) q)
                            (cpow p (cscale (ch qbi) gb) q))
    by (apply ccong_cpow; [ exact Hp1' | exact Hg ]).
  apply (ccong_trans p _ _ (cpow p (cpow p g q) q)).
  { apply ccong_of_beq. unfold QQ. apply cpow_mul; exact Hp1'. }
  apply (ccong_trans p _ _ (cpow p (cscale (ch qbi) gb) q)); [ exact H2 | ].
  apply (ccong_trans p _ _ (cscale (epow (ch qbi) q) (cpow p gb q)));
    [ apply ccong_of_beq, cscale_cpow; exact Hp1' | ].
  assert (Hc : epow (ch qbi) q = econj (ch qbi)).
  { apply cuberoot_pow_2mod3; [ | exact Hq2 ].
    apply (chn_cuberoot p pi Hp Hp7 Hnp). exact qbi_range. }
  rewrite Hc.
  apply (ccong_trans p _ _ (cscale (econj (ch qbi)) (cscale (econj (ch qbi)) g)));
    [ apply ccong_cscale; exact Hgb | ].
  apply ccong_of_beq. intros u _. unfold cscale.
  assert (E : emul (econj (ch qbi)) (emul (econj (ch qbi)) (g u))
              = emul (emul (econj (ch qbi)) (econj (ch qbi))) (g u)) by ring.
  rewrite E, (cuberoot_conj_sq (ch qbi)
                (chn_cuberoot p pi Hp Hp7 Hnp qbi qbi_range)). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  relation (A) for the inert case                                *)
(* ----------------------------------------------------------------- *)
Theorem relation_A_inert : chiq q SJ' = ch qbi.
Proof.
  assert (HA : ceq p (cpow p g (QQ - 1)%nat) (cemb p (epow SJ' mmi))).
  { rewrite <- mmi_spec.
    apply (ceq_trans p _ (cpow p (cpow p g 3) mmi));
      [ apply beq_ceq, cpow_mul; exact Hp1' | ].
    apply (ceq_trans p _ (cpow p (cemb p SJ') mmi)).
    { apply ceq_cpow; [ exact Hp1' | ].
      exact (gauss_cube p pi t0 Hp Hp7 Hdivp Hnp Htp). }
    apply beq_ceq, beq_sym, cemb_pow; exact Hp1'. }
  assert (HB : ceq p (cpow p g QQ) (cmul p g (cemb p (epow SJ' mmi)))).
  { assert (Hqs : QQ = S (QQ - 1)%nat) by nia.
    rewrite Hqs at 1.
    replace (cpow p g (S (QQ - 1)%nat))
      with (cmul p g (cpow p g (QQ - 1)%nat)) by reflexivity.
    apply ceq_cmul_r; [ exact Hp1' | exact HA ]. }
  assert (HD : qceq p (eZ Q) (cmul p g (cemb p (epow SJ' mmi)))
                          (cscale (ch qbi) g)).
  { apply (qceq_trans p _ _ (cpow p g QQ)).
    - apply qceq_sym, qceq_of_ceq. exact HB.
    - apply qceq_of_ccong. exact frob_twice. }
  assert (Hgg : ceq p (cmul p g gb) (cemb p (eZ P))).
  { apply (ceq_trans p _ (csub (cscale (eZ P) (cone p)) cN)).
    - apply beq_ceq. exact (gauss_norm p pi t0 Hp Hp7 Hdivp Hnp Htp).
    - intros u v _ _. unfold csub, cemb, cscale, cN. ring. }
  assert (HE : qceq p (eZ Q) (cemb p (emul (eZ P) (epow SJ' mmi)))
                          (cemb p (emul (ch qbi) (eZ P)))).
  { apply (qceq_trans p _ _ (cmul p gb (cmul p g (cemb p (epow SJ' mmi))))).
    { apply qceq_sym.
      apply (qceq_trans p _ _ (cmul p (cmul p g gb) (cemb p (epow SJ' mmi))));
        [ apply qceq_of_beq; ring | ].
      apply (qceq_trans p _ _ (cmul p (cemb p (eZ P)) (cemb p (epow SJ' mmi))));
        [ apply qceq_of_ceq, ceq_cmul_l; [ exact Hp1' | exact Hgg ] | ].
      apply qceq_of_beq, beq_sym, cemb_mul; exact Hp1'. }
    apply (qceq_trans p _ _ (cmul p gb (cscale (ch qbi) g)));
      [ apply qceq_cmul_r; [ exact Hp1' | exact HD ] | ].
    apply (qceq_trans p _ _ (cscale (ch qbi) (cmul p gb g))).
    { apply qceq_of_beq. intros u _. unfold cscale, cmul.
      rewrite <- (Esum_scale_l (ch qbi)
                    (fun i => emul (gb i) (g (msub p u i))) (seq 0 p)).
      apply Esum_ext. intros i _. ring. }
    apply (qceq_trans p _ _ (cscale (ch qbi) (cmul p g gb)));
      [ apply qceq_of_beq, beq_cscale, cmul_comm; exact Hp1' | ].
    apply (qceq_trans p _ _ (cscale (ch qbi) (cemb p (eZ P))));
      [ apply qceq_of_ceq, ceq_cscale; exact Hgg | ].
    apply qceq_of_beq. intros u _. unfold cemb, cscale. ring. }
  assert (HF : edvd (eZ Q) (esub (emul (eZ P) (epow SJ' mmi))
                                 (emul (ch qbi) (eZ P))))
    by (apply (qceq_cemb p Hp1' Hp2'); exact HE).
  assert (HG : econg (eZ Q) (epow SJ' mmi) (ch qbi)).
  { destruct HF as [c Hc].
    assert (E : esub (emul (eZ P) (epow SJ' mmi)) (emul (ch qbi) (eZ P))
                = emul (eZ P) (esub (epow SJ' mmi) (ch qbi))) by ring.
    rewrite E in Hc.
    destruct (irred_prime (eZ Q) (eZ P) (esub (epow SJ' mmi) (ch qbi))
                (q_irred q Hq Hq2) ltac:(exists c; exact Hc)) as [H | H];
      [ exfalso; exact (theta_ndvd_p_i H) | exact H ]. }
  pose proof (chiq_cong q Hq Hq2 Hq5 SJ' theta_ndvd_SJ_i) as HEu.
  apply (cuberoot_unique (eZ Q) (Z.of_nat QQ) (epow SJ' mmi)).
  - exact qq_norm'.
  - nia.
  - apply (chiq_cuberoot q Hq Hq2). exact theta_ndvd_SJ_i.
  - apply (chn_cuberoot p pi Hp Hp7 Hnp). exact qbi_range.
  - exact HEu.
  - exact HG.
Qed.

(* ----------------------------------------------------------------- *)
(*  F.  CUBIC RECIPROCITY, INERT CASE                                  *)
(* ----------------------------------------------------------------- *)
Lemma cuberoot_collapse2 : forall z, cuberoot z ->
  emul (emul z (econj z)) z = z.
Proof. intros z [-> | [-> | ->]]; reflexivity. Qed.

Theorem cubic_reciprocity_inert : chiq q pi = chn p pi q.
Proof.
  assert (HJ : Jsum p pi = pi)
    by (apply (Jsum_primary_eq p pi t0); assumption).
  assert (Hpp : eZ P = emul pi (econj pi))
    by (rewrite emul_econj, Hnp; reflexivity).
  pose proof relation_A_inert as HA.
  unfold SJ' in HA. rewrite HJ, Hpp in HA.
  rewrite !(chiq_mul q Hq Hq2 Hq5) in HA.
  rewrite (chiq_conj q Hq Hq2 Hq5 pi theta_ndvd_pi) in HA.
  rewrite (cuberoot_collapse2 (chiq q pi)
             (chiq_cuberoot q Hq Hq2 pi theta_ndvd_pi)) in HA.
  rewrite HA. unfold qbi.
  exact (chiv_mod p pi t0 Hp Hp7 Hdivp Hnp Htp q).
Qed.

End RecInert.

Print Assumptions relation_A_inert.
Print Assumptions cubic_reciprocity_inert.
