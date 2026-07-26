(* ================================================================= *)
(*  ZetaSquareConstructive.v                                        *)
(*                                                                    *)
(*  ∑_{n≤N} τ(n)/n²  →  ζ(2)²   AS AN AXIOM-FREE STATEMENT over the    *)
(*  constructive real `zeta2c` (ZetaConstructive) — the de-quarantined *)
(*  analytic ζ².                                                      *)
(*                                                                    *)
(*  The hyperbola combinatorics is redone over ℚ (`qsum`); the        *)
(*  convergence is assembled with the `CReal` calculus of CRealCv     *)
(*  (`cvQ_squeeze`, `cvQ_sq`, `cvQ_reindex`, `cvQ_eventually_eq`).     *)
(*                                                                    *)
(*     cvQ DpartQ (zeta2c * zeta2c)   :  ∑_{n≤N} τ(n)/n² → ζ(2)².     *)
(*                                                                    *)
(*  `Print Assumptions` = Closed under the global context.           *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import ZArith QArith Qabs Qround Lqa Lia List Arith Permutation.
Import ListNotations.
Require Import PrimonGas CRealCv ZetaConstructive Totient JacobiRHS R2Count.
Local Open Scope Q_scope.

(* ================================================================= *)
(*  ℚ weights                                                         *)
(* ================================================================= *)
Definition qw (a : nat) : Q := / (qN a * qN a).
Definition qwp (ab : nat * nat) : Q := qw (fst ab) * qw (snd ab).
Definition taun (n : nat) : nat := length (divisors n).

Lemma qN_nonneg : forall a, 0 <= qN a.
Proof. intro a; unfold qN; change 0 with (inject_Z 0); rewrite <- Zle_Qle; lia. Qed.

Lemma qw_nonneg : forall a, 0 <= qw a.
Proof.
  intro a; unfold qw; apply Qinv_le_0_compat, Qmult_le_0_compat; apply qN_nonneg.
Qed.

Lemma qwp_nonneg : forall ab, 0 <= qwp ab.
Proof. intro ab; unfold qwp; apply Qmult_le_0_compat; apply qw_nonneg. Qed.

Lemma qw_mul : forall a b, qw (a * b)%nat == qw a * qw b.
Proof.
  intros a b; unfold qw.
  assert (E : qN (a * b)%nat * qN (a * b)%nat == (qN a * qN a) * (qN b * qN b)).
  { assert (H : qN (a * b)%nat == qN a * qN b)
      by (unfold qN; rewrite Nat2Z.inj_mul, inject_Z_mult; reflexivity).
    rewrite H; ring. }
  rewrite E, Qinv_mult_distr; reflexivity.
Qed.

(* ================================================================= *)
(*  ℚ finite-sum toolkit (ports of the R-level Rlsum lemmas)          *)
(* ================================================================= *)
Lemma qsum_prodsep : forall (f g : nat -> Q) l1 l2,
  qsum (map (fun ab => f (fst ab) * g (snd ab)) (list_prod l1 l2))
  == qsum (map f l1) * qsum (map g l2).
Proof.
  intros f g l1 l2; induction l1 as [|a l1 IH]; [ simpl; ring | ].
  simpl list_prod; rewrite map_app, qsum_app, IH, map_map; cbn [fst snd].
  rewrite (qsum_map_scale_l _ (f a) g l2); cbn [map qsum]; ring.
Qed.

Lemma qsum_perm : forall l l', Permutation l l' -> qsum l == qsum l'.
Proof.
  intros l l' H; induction H.
  - reflexivity.
  - cbn [qsum]; rewrite IHPermutation; reflexivity.
  - cbn [qsum]; ring.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma qsum_const : forall {A} (h : A -> Q) l c,
  (forall x, In x l -> h x == c) -> qsum (map h l) == qN (length l) * c.
Proof.
  intros A h l c H; induction l as [|a l IH].
  - simpl; unfold qN; simpl; ring.
  - cbn [map qsum length]; rewrite (H a (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply H; right; exact Hx).
    rewrite (qN_succ (length l)); ring.
Qed.

(* NoDup-domination for the pair weight qwp *)
Definition pnat_eq_dec : forall x y : nat * nat, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Lemma remove_nodup_p : forall x l, NoDup l -> NoDup (remove pnat_eq_dec x l).
Proof.
  intros x l; induction l as [|a l IH]; intro Hnd; simpl; [ constructor | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  destruct (pnat_eq_dec x a) as [He | Hne]; [ apply IH; exact Hnd' | ].
  constructor;
    [ intro Hin; apply in_remove in Hin; destruct Hin as [Hin _]; contradiction
    | apply IH; exact Hnd' ].
Qed.

Lemma qsum_remove_w : forall r l, In r l -> NoDup l ->
  qsum (map qwp l) == qwp r + qsum (map qwp (remove pnat_eq_dec r l)).
Proof.
  intros r l; induction l as [|a l IH]; intros Hin Hnd; [ destruct Hin | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  cbn [map remove]; destruct (pnat_eq_dec r a) as [He | Hne].
  - subst a; rewrite (notin_remove pnat_eq_dec l r Hnin); cbn [map qsum]; reflexivity.
  - destruct Hin as [Ha | Hin]; [ symmetry in Ha; contradiction | ].
    cbn [map qsum]; rewrite (IH Hin Hnd'); ring.
Qed.

Lemma qsum_incl_le_w : forall Rs L,
  NoDup L -> incl L Rs -> qsum (map qwp L) <= qsum (map qwp Rs).
Proof.
  induction Rs as [|r R' IH]; intros L Hnd Hincl.
  - assert (L = []).
    { destruct L as [|a L0]; [ reflexivity | exfalso; destruct (Hincl a (in_eq a L0)) ]. }
    subst; simpl; apply Qle_refl.
  - cbn [map qsum]; destruct (in_dec pnat_eq_dec r L) as [Hin | Hnin].
    + rewrite (qsum_remove_w r L Hin Hnd).
      apply Qplus_le_r, IH; [ apply remove_nodup_p; exact Hnd | ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin'];
        [ exfalso; apply Hx2; symmetry; exact He | exact Hin' ].
    + apply Qle_trans with (qsum (map qwp R')).
      * apply IH; [ exact Hnd | ].
        intros x Hx; destruct (Hincl x Hx) as [He | Hin'];
          [ subst r; contradiction | exact Hin' ].
      * pose proof (qwp_nonneg r); lra.
Qed.

(* ================================================================= *)
(*  the 1-D partial sums SMQ, its bound by 2, and its limit           *)
(* ================================================================= *)
Definition SMQ (M : nat) : Q := qsum (map qw (seq 1 M)).

Lemma SMQ_S : forall M, SMQ (S M) == SMQ M + qw (S M).
Proof.
  intro M; unfold SMQ.
  replace (seq 1 (S M)) with (seq 1 M ++ [S M]) by (rewrite <- seq_S; reflexivity).
  rewrite map_app, qsum_app; cbn [map qsum]; ring.
Qed.

Lemma SMQ_eq_zpartQ : forall N, SMQ (S N) == zpartQ N.
Proof.
  induction N as [|N IH].
  - reflexivity.
  - rewrite SMQ_S, IH, zpartQ_S; reflexivity.
Qed.

Lemma SMQ_nonneg : forall M, 0 <= SMQ M.
Proof.
  intro M; unfold SMQ; induction (seq 1 M) as [|a l IH]; [ apply Qle_refl | ].
  cbn [map qsum]; pose proof (qw_nonneg a); lra.
Qed.

Lemma zpartQ_le2 : forall N, zpartQ N <= 2.
Proof.
  intro N; pose proof (zpartQ_tail 0 N (Nat.le_0_l N)) as H.
  assert (Hz0 : zpartQ 0 == 1) by reflexivity.
  assert (Hinv0 : inv_np 0 == 1) by reflexivity.
  lra.
Qed.

Lemma SMQ_le2 : forall M, Qabs (SMQ M) <= 2.
Proof.
  intro M; rewrite Qabs_pos by apply SMQ_nonneg.
  destruct M as [|M']; [ simpl; unfold SMQ; simpl; lra | ].
  rewrite SMQ_eq_zpartQ; apply zpartQ_le2.
Qed.

Lemma SMQ_cv : cvQ SMQ zeta2c.
Proof.
  apply (cvQ_eventually_eq SMQ (fun M => zpartQ (M - 1)) zeta2c 1).
  - intros n Hn; destruct n as [|n']; [ lia | ].
    replace (S n' - 1)%nat with n' by lia; apply SMQ_eq_zpartQ.
  - apply (cvQ_reindex zpartQ zeta2c (fun M => M - 1)%nat).
    + apply zeta2c_cv.
    + intro m; exists (S m); intros n Hn; lia.
Qed.

(* ================================================================= *)
(*  hyperbola pieces over ℚ                                           *)
(* ================================================================= *)
Definition boxQ (M : nat) : Q := qsum (map qwp (list_prod (seq 1 M) (seq 1 M))).
Definition pairboxQ (N : nat) : list (nat * nat) :=
  filter (fun ab => (fst ab * snd ab <=? N)%nat) (list_prod (seq 1 N) (seq 1 N)).
Definition SpartQ (N : nat) : Q := qsum (map qwp (pairboxQ N)).
Definition DpartQ (N : nat) : Q := qsum (map (fun n => qN (taun n) * qw n) (seq 1 N)).
Definition divpairs (n : nat) : list (nat * nat) := map (fun d => (d, (n / d)%nat)) (divisors n).

Lemma box_sq : forall M, boxQ M == SMQ M * SMQ M.
Proof. intro M; unfold boxQ, qwp, SMQ; apply qsum_prodsep. Qed.

Lemma box_lower : forall N, boxQ (Nat.sqrt N) <= SpartQ N.
Proof.
  intro N; unfold boxQ, SpartQ; apply qsum_incl_le_w.
  - apply NoDup_list_prod; apply seq_NoDup.
  - intros ab Hab; destruct ab as [a b]; apply in_prod_iff in Hab; destruct Hab as [Ha Hb].
    apply in_seq in Ha; apply in_seq in Hb.
    unfold pairboxQ; apply filter_In; split.
    + apply in_prod; apply in_seq; split; try (pose proof (Nat.sqrt_le_lin N); lia).
    + apply Nat.leb_le; cbn [fst snd].
      destruct (Nat.sqrt_spec N (Nat.le_0_l N)) as [Hsq _].
      apply Nat.le_trans with (Nat.sqrt N * Nat.sqrt N)%nat;
        [ apply Nat.mul_le_mono; lia | exact Hsq ].
Qed.

Lemma Spart_le_box : forall N, SpartQ N <= boxQ N.
Proof.
  intro N; unfold SpartQ, boxQ; apply qsum_incl_le_w.
  - apply NoDup_filter, NoDup_list_prod; apply seq_NoDup.
  - unfold pairboxQ; intros ab Hab; apply filter_In in Hab; tauto.
Qed.

(* ================================================================= *)
(*  the τ bridge over ℚ                                               *)
(* ================================================================= *)
Lemma divpairs_sum : forall n, qsum (map qwp (divpairs n)) == qN (taun n) * qw n.
Proof.
  intro n; unfold divpairs; rewrite map_map.
  rewrite (qsum_const (fun d => qwp (d, (n / d)%nat)) (divisors n) (qw n)).
  - unfold taun; reflexivity.
  - intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 _] Hmod].
    unfold qwp; cbn [fst snd]; rewrite <- qw_mul.
    apply Nat.Lcm0.mod_divide in Hmod; destruct Hmod as [c Hc]; subst n.
    rewrite Nat.div_mul by lia; rewrite Nat.mul_comm; reflexivity.
Qed.

Lemma NoDup_flat_map_disjoint : forall {A B} (f : A -> list B) (l : list A),
  NoDup l -> (forall a, In a l -> NoDup (f a)) ->
  (forall a1 a2 x, In a1 l -> In a2 l -> In x (f a1) -> In x (f a2) -> a1 = a2) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hnd Hnda Hdisj; [ constructor | ].
  cbn [flat_map]; inversion Hnd as [| ? ? Hnin Hnd']; subst.
  apply NoDup_app.
  - apply Hnda; left; reflexivity.
  - apply IH; [ exact Hnd' | intros a' Ha'; apply Hnda; right; exact Ha'
              | intros a1 a2 x H1 H2; apply Hdisj; right; assumption ].
  - intros x Hx Hx2; apply in_flat_map in Hx2; destruct Hx2 as [a' [Ha' Hxa']].
    assert (a = a') by (apply (Hdisj a a' x); [ left; reflexivity | right; exact Ha' | exact Hx | exact Hxa' ]).
    subst a'; contradiction.
Qed.

Lemma pairbox_perm : forall N, Permutation (pairboxQ N) (flat_map divpairs (seq 1 N)).
Proof.
  intro N; apply NoDup_Permutation.
  - apply NoDup_filter, NoDup_list_prod; apply seq_NoDup.
  - apply NoDup_flat_map_disjoint.
    + apply seq_NoDup.
    + intros a _; unfold divpairs; apply NoDup_map_inj;
        [ intros x y _ _ Hxy; injection Hxy; auto | apply divisors_nodup ].
    + intros n1 n2 x _ _ Hx1 Hx2; unfold divpairs in *.
      apply in_map_iff in Hx1; destruct Hx1 as [d1 [He1 Hd1]].
      apply in_map_iff in Hx2; destruct Hx2 as [d2 [He2 Hd2]].
      apply in_divisors in Hd1; apply in_divisors in Hd2.
      destruct Hd1 as [[Hd1a _] Hm1]; destruct Hd2 as [[Hd2a _] Hm2].
      apply Nat.Lcm0.mod_divide in Hm1; apply Nat.Lcm0.mod_divide in Hm2.
      rewrite <- He1 in He2; injection He2 as Hf Hs.
      destruct Hm1 as [c1 Hc1]; destruct Hm2 as [c2 Hc2]; subst n1 n2.
      rewrite (Nat.div_mul c1 d1) in Hs by lia;
        rewrite (Nat.div_mul c2 d2) in Hs by lia; subst; nia.
  - intro ab; destruct ab as [a b]; split.
    + unfold pairboxQ; rewrite filter_In; intros [Hin Hle].
      apply in_prod_iff in Hin; destruct Hin as [Ha Hb].
      apply in_seq in Ha; apply in_seq in Hb; apply Nat.leb_le in Hle; cbn [fst snd] in Hle.
      apply in_flat_map; exists (a * b)%nat; split.
      * apply in_seq; nia.
      * unfold divpairs; apply in_map_iff; exists a; split.
        -- f_equal; replace (a * b)%nat with (b * a)%nat by ring;
             rewrite Nat.div_mul by lia; reflexivity.
        -- apply in_divisors; split; [ nia | apply Nat.Lcm0.mod_divide; exists b; ring ].
    + rewrite in_flat_map; intros [n [Hn Hab]].
      apply in_seq in Hn; unfold divpairs in Hab; apply in_map_iff in Hab.
      destruct Hab as [d [Hd Hdin]]; injection Hd as Hda Hdb.
      apply in_divisors in Hdin; destruct Hdin as [[Hd1 Hd2] Hmod].
      apply Nat.Lcm0.mod_divide in Hmod; destruct Hmod as [c Hc].
      subst a n; rewrite Nat.div_mul in Hdb by lia; subst b.
      unfold pairboxQ; apply filter_In; split.
      * apply in_prod; apply in_seq; nia.
      * apply Nat.leb_le; cbn [fst snd]; nia.
Qed.

Lemma Spart_eq_Dpart : forall N, SpartQ N == DpartQ N.
Proof.
  intro N; unfold SpartQ, DpartQ.
  rewrite (qsum_perm _ _ (Permutation_map qwp (pairbox_perm N))).
  rewrite qsum_map_flat_map.
  apply qsum_map_ext; intro n; apply divpairs_sum.
Qed.

(* ================================================================= *)
(*  convergence assembly:  ∑τ(n)/n²  →  ζ(2)²                        *)
(* ================================================================= *)
Lemma boxQ_cv : cvQ boxQ (zeta2c * zeta2c)%CReal.
Proof.
  apply (cvQ_eventually_eq boxQ (fun M => (SMQ M * SMQ M)%Q) (zeta2c * zeta2c)%CReal 0).
  - intros n _; apply box_sq.
  - apply cvQ_sq; [ apply SMQ_cv | apply SMQ_le2 ].
Qed.

Lemma boxQ_sqrt_cv : cvQ (fun N => boxQ (Nat.sqrt N)) (zeta2c * zeta2c)%CReal.
Proof.
  apply (cvQ_reindex boxQ (zeta2c * zeta2c)%CReal Nat.sqrt).
  - apply boxQ_cv.
  - intro m; exists (m * m)%nat; intros n Hn.
    apply Nat.le_trans with (Nat.sqrt (m * m));
      [ rewrite Nat.sqrt_square; lia | apply Nat.sqrt_le_mono; lia ].
Qed.

Theorem SpartQ_cv : cvQ SpartQ (zeta2c * zeta2c)%CReal.
Proof.
  apply (cvQ_squeeze (fun N => boxQ (Nat.sqrt N)) SpartQ boxQ (zeta2c * zeta2c)%CReal).
  - apply boxQ_sqrt_cv.
  - apply boxQ_cv.
  - apply box_lower.
  - apply Spart_le_box.
Qed.

Theorem zeta_two_sq_tau_constructive : cvQ DpartQ (zeta2c * zeta2c)%CReal.
Proof.
  apply (cvQ_eventually_eq DpartQ SpartQ (zeta2c * zeta2c)%CReal 0).
  - intros n _; symmetry; apply Spart_eq_Dpart.
  - apply SpartQ_cv.
Qed.

(* axiom-free companion to ZetaMaster: ζ(2) as a CReal and its square *)
Theorem zeta_square_constructive :
  cvQ zpartQ zeta2c /\
  (forall N, SpartQ N == DpartQ N) /\
  cvQ SpartQ (zeta2c * zeta2c)%CReal /\
  cvQ DpartQ (zeta2c * zeta2c)%CReal.
Proof.
  exact (conj zeta2c_cv (conj Spart_eq_Dpart (conj SpartQ_cv zeta_two_sq_tau_constructive))).
Qed.

Print Assumptions zeta_square_constructive.

(* ================================================================= *)
(*  END ZetaSquareConstructive.v                                    *)
(*  ∑_{n≤N} τ(n)/n² → ζ(2)² over the constructive real zeta2c.        *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
