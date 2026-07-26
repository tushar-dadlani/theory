(* ================================================================= *)
(*  ZetaSquareAnalytic.v                                             *)
(*                                                                    *)
(*  THE ANALYTIC ZETA-SQUARED:   ∑_{n≥1} τ(n)/n²  =  ζ(2)².          *)
(*                                                                    *)
(*  The Dirichlet series of the divisor function τ at s=2 converges   *)
(*  to ζ(2)², proved by the classical HYPERBOLA SQUEEZE:             *)
(*                                                                    *)
(*     Σ_{n≤N} τ(n)/n²  =  Σ_{a·b≤N} 1/(a·b)²                        *)
(*     box(⌊√N⌋)  ≤  Σ_{a·b≤N} 1/(a·b)²  ≤  box(N)                  *)
(*     box(M) = (Σ_{a≤M} 1/a²)²  →  ζ(2)²   (both bounds)            *)
(*                                                                    *)
(*  built on the repo's ζ(2) arc (ZetaConverge / RecipSquareBound).   *)
(*                                                                    *)
(*  NOT axiom-free: like the whole ζ(2) arc this rests on the         *)
(*  classical Reals axioms (quarantined).  ζ(2)'s value π²/6 is out   *)
(*  of scope — the result is convergence to (proj1_sig               *)
(*  zeta2_converges)².                                                *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List Permutation Arith ZArith.
Import ListNotations.
Require Import ZetaConverge RecipSquareBound R2Count Totient DirichletConv
        DirichletMult DirichletDivisor JacobiRHS.
Open Scope R_scope.

Definition Lz : R := proj1_sig zeta2_converges.

(* ================================================================= *)
(*  Part 0 — R-sum helpers and small convergence lemmas              *)
(* ================================================================= *)

(* rr is completely multiplicative on the reciprocal-square weight    *)
Lemma rr_mul : forall a b, rr (a * b)%nat = rr a * rr b.
Proof.
  intros a b; unfold rr; rewrite mult_INR.
  replace ((INR a * INR b) ^ 2) with ((INR a) ^ 2 * (INR b) ^ 2) by ring.
  rewrite Rinv_mult; reflexivity.
Qed.

Lemma Rlsum_scale : forall {A} (c : R) (f : A -> R) (l : list A),
  Rlsum (map (fun x => c * f x) l) = c * Rlsum (map f l).
Proof.
  intros A c f l; induction l as [|a l IH]; [ unfold Rlsum; simpl; ring | ].
  cbn [map]; rewrite !Rlsum_cons, IH; ring.
Qed.

Lemma Rlsum_prodsep : forall (f g : nat -> R) l1 l2,
  Rlsum (map (fun ab => f (fst ab) * g (snd ab)) (list_prod l1 l2))
  = Rlsum (map f l1) * Rlsum (map g l2).
Proof.
  intros f g l1 l2; induction l1 as [|a l1 IH]; [ unfold Rlsum; simpl; ring | ].
  simpl list_prod; rewrite map_app, Rlsum_app, IH, map_map; cbn [fst snd].
  rewrite (Rlsum_scale (f a) g l2); cbn [map]; rewrite Rlsum_cons; ring.
Qed.

Lemma Rlsum_const : forall {A} (h : A -> R) l c,
  (forall x, In x l -> h x = c) -> Rlsum (map h l) = INR (length l) * c.
Proof.
  intros A h l c H; induction l as [|a l IH]; [ unfold Rlsum; simpl; ring | ].
  cbn [map length]; rewrite Rlsum_cons, (H a (in_eq _ _)), IH by (intros x Hx; apply H; right; exact Hx).
  rewrite S_INR; ring.
Qed.

Lemma Rlsum_perm : forall (l l' : list R), Permutation l l' -> Rlsum l = Rlsum l'.
Proof.
  intros l l' H; induction H.
  - reflexivity.
  - rewrite !Rlsum_cons, IHPermutation; reflexivity.
  - rewrite !Rlsum_cons; ring.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma Rlsum_map_flat_map : forall {A B} (g : B -> R) (h : A -> list B) (l : list A),
  Rlsum (map g (flat_map h l)) = Rlsum (map (fun a => Rlsum (map g (h a))) l).
Proof.
  intros A B g h l; induction l as [|a l IH]; [ reflexivity | ].
  cbn [flat_map]; rewrite map_app, Rlsum_app, IH; cbn [map]; rewrite Rlsum_cons; reflexivity.
Qed.

(* the pair weight w(a,b) = 1/a² · 1/b²  ( = 1/(ab)² ) *)
Definition w (ab : nat * nat) : R := rr (fst ab) * rr (snd ab).

Lemma w_nonneg : forall ab, 0 <= w ab.
Proof. intro ab; unfold w; apply Rmult_le_pos; apply rr_nonneg. Qed.

(* pair-list "included ⇒ sum ≤" (port of RecipSquareBound.incl_sum_le to nat*nat, g = w) *)
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

Lemma sum_remove_w : forall r l, In r l -> NoDup l ->
  Rlsum (map w l) = w r + Rlsum (map w (remove pnat_eq_dec r l)).
Proof.
  intros r l; induction l as [|a l IH]; intros Hin Hnd; [ destruct Hin | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  cbn [map remove]; rewrite Rlsum_cons.
  destruct (pnat_eq_dec r a) as [He | Hne].
  - subst a; rewrite (notin_remove pnat_eq_dec l r Hnin); reflexivity.
  - destruct Hin as [Ha | Hin]; [ symmetry in Ha; contradiction | ].
    cbn [map]; rewrite Rlsum_cons, (IH Hin Hnd'); ring.
Qed.

Lemma incl_sum_le_w : forall Rs L,
  NoDup L -> incl L Rs -> Rlsum (map w L) <= Rlsum (map w Rs).
Proof.
  induction Rs as [|r R' IH]; intros L Hnd Hincl.
  - assert (L = []).
    { destruct L as [|a L0]; [ reflexivity | ].
      exfalso; destruct (Hincl a (in_eq a L0)). }
    subst; unfold Rlsum; simpl; lra.
  - cbn [map]; rewrite Rlsum_cons.
    destruct (in_dec pnat_eq_dec r L) as [Hin | Hnin].
    + rewrite (sum_remove_w r L Hin Hnd).
      apply Rplus_le_compat_l.
      apply IH; [ apply remove_nodup_p; exact Hnd | ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin'];
        [ exfalso; apply Hx2; symmetry; exact He | exact Hin' ].
    + apply Rle_trans with (Rlsum (map w R')).
      * apply IH; [ exact Hnd | ].
        intros x Hx; destruct (Hincl x Hx) as [He | Hin'];
          [ subst r; contradiction | exact Hin' ].
      * pose proof (w_nonneg r); lra.
Qed.

(* small convergence facts (ε-N), local to avoid importing the Euler arc *)
Lemma Un_cv_eventually_eq : forall u v L K,
  (forall n, (K <= n)%nat -> u n = v n) -> Un_cv v L -> Un_cv u L.
Proof.
  intros u v L K Heq Hv eps Heps.
  destruct (Hv eps Heps) as [N HN].
  exists (Nat.max N K); intros n Hn.
  rewrite Heq by lia; apply HN; lia.
Qed.

Lemma Un_cv_reindex : forall u L (phi : nat -> nat), Un_cv u L ->
  (forall m, exists K, forall n, (K <= n)%nat -> (m <= phi n)%nat) ->
  Un_cv (fun n => u (phi n)) L.
Proof.
  intros u L phi Hu Hdiv eps Heps.
  destruct (Hu eps Heps) as [M HM].
  destruct (Hdiv M) as [K HK].
  exists K; intros n Hn; apply HM, HK; lia.
Qed.

Lemma squeeze_const_upper : forall a u L,
  Un_cv a L -> (forall N, a N <= u N) -> (forall N, u N <= L) -> Un_cv u L.
Proof.
  intros a u L Ha Hlo Hhi eps Heps.
  destruct (Ha eps Heps) as [N HN]; exists N; intros n Hn.
  specialize (HN n Hn); apply Rabs_def2 in HN; destruct HN as [H1 H2].
  unfold R_dist; apply Rabs_def1; [ specialize (Hhi n); lra | specialize (Hlo n); lra ].
Qed.

(* ================================================================= *)
(*  Part 1 — the hyperbola squeeze:  Σ_{ab≤N} 1/(ab)² → ζ(2)²        *)
(* ================================================================= *)
Definition box (M : nat) : R := Rlsum (map w (list_prod (seq 1 M) (seq 1 M))).

Definition pairbox (N : nat) : list (nat * nat) :=
  filter (fun ab => (fst ab * snd ab <=? N)%nat) (list_prod (seq 1 N) (seq 1 N)).

Definition Spart (N : nat) : R := Rlsum (map w (pairbox N)).

Lemma box_sq : forall M, box M = Rlsum (map rr (seq 1 M)) * Rlsum (map rr (seq 1 M)).
Proof. intro M; unfold box, w; rewrite (Rlsum_prodsep rr rr (seq 1 M) (seq 1 M)); reflexivity. Qed.

Lemma box_lower : forall N, box (Nat.sqrt N) <= Spart N.
Proof.
  intro N; unfold box, Spart.
  apply incl_sum_le_w.
  - apply NoDup_list_prod; apply seq_NoDup.
  - intros ab Hab; destruct ab as [a b]; apply in_prod_iff in Hab; destruct Hab as [Ha Hb].
    apply in_seq in Ha; apply in_seq in Hb.
    unfold pairbox; apply filter_In; split.
    + apply in_prod; apply in_seq; split;
        try (pose proof (Nat.sqrt_le_lin N); lia).
    + apply Nat.leb_le; cbn [fst snd].
      destruct (Nat.sqrt_spec N (Nat.le_0_l N)) as [Hsq _].
      apply Nat.le_trans with (Nat.sqrt N * Nat.sqrt N)%nat;
        [ apply Nat.mul_le_mono; lia | exact Hsq ].
Qed.

Lemma Rlsum_map_rr_nonneg : forall l, 0 <= Rlsum (map rr l).
Proof.
  induction l as [|a l IH]; [ unfold Rlsum; simpl; lra | ].
  cbn [map]; rewrite Rlsum_cons; pose proof (rr_nonneg a); lra.
Qed.

Lemma SM_le_Lz : forall M, Rlsum (map rr (seq 1 M)) <= Lz.
Proof.
  intro M; destruct M as [|M'].
  - cbn [seq map]; unfold Rlsum; simpl; apply Lz_nonneg.
  - rewrite seqsum_zpart; apply growing_ineq;
      [ apply zpart_growing | apply (proj2_sig zeta2_converges) ].
Qed.

Lemma box_le_Lz2 : forall M, box M <= Lz * Lz.
Proof.
  intro M; rewrite box_sq.
  apply Rmult_le_compat;
    [ apply Rlsum_map_rr_nonneg | apply Rlsum_map_rr_nonneg | apply SM_le_Lz | apply SM_le_Lz ].
Qed.

Lemma Spart_le_box : forall N, Spart N <= box N.
Proof.
  intro N; unfold Spart, box; apply incl_sum_le_w.
  - apply NoDup_filter, NoDup_list_prod; apply seq_NoDup.
  - unfold pairbox; intros ab Hab; apply filter_In in Hab; tauto.
Qed.

Lemma Spart_upper : forall N, Spart N <= Lz * Lz.
Proof. intro N; apply Rle_trans with (box N); [ apply Spart_le_box | apply box_le_Lz2 ]. Qed.

Lemma SM_cv : Un_cv (fun M => Rlsum (map rr (seq 1 M))) Lz.
Proof.
  apply (Un_cv_eventually_eq _ (fun M => zpart (M - 1)) Lz 1).
  - intros M HM; destruct M as [|M']; [ lia | rewrite seqsum_zpart; f_equal; lia ].
  - apply (Un_cv_reindex zpart Lz (fun M => M - 1)%nat).
    + apply (proj2_sig zeta2_converges).
    + intro m; exists (S m); intros n Hn; lia.
Qed.

Lemma low_cv : Un_cv (fun N => box (Nat.sqrt N)) (Lz * Lz).
Proof.
  apply (Un_cv_eventually_eq _
           (fun N => Rlsum (map rr (seq 1 (Nat.sqrt N))) * Rlsum (map rr (seq 1 (Nat.sqrt N))))
           (Lz * Lz) 0).
  - intros N _; apply box_sq.
  - apply CV_mult;
      apply (Un_cv_reindex (fun M => Rlsum (map rr (seq 1 M))) Lz Nat.sqrt);
      [ apply SM_cv
      | intro m; exists (m * m)%nat; intros n Hn;
        apply Nat.le_trans with (Nat.sqrt (m * m));
          [ rewrite Nat.sqrt_square; lia | apply Nat.sqrt_le_mono; lia ]
      | apply SM_cv
      | intro m; exists (m * m)%nat; intros n Hn;
        apply Nat.le_trans with (Nat.sqrt (m * m));
          [ rewrite Nat.sqrt_square; lia | apply Nat.sqrt_le_mono; lia ] ].
Qed.

Theorem zeta_two_sq_hyperbola : Un_cv Spart (Lz * Lz).
Proof.
  apply (squeeze_const_upper (fun N => box (Nat.sqrt N)) Spart (Lz * Lz)).
  - apply low_cv.
  - apply box_lower.
  - apply Spart_upper.
Qed.

(* ================================================================= *)
(*  Part 2 — the τ bridge:  Spart N = Σ_{n≤N} τ(n)/n²               *)
(* ================================================================= *)
Definition taun (n : nat) : nat := length (divisors n).
Definition Dpart (N : nat) : R := Rlsum (map (fun n => INR (taun n) * rr n) (seq 1 N)).
Definition divpairs (n : nat) : list (nat * nat) := map (fun d => (d, (n / d)%nat)) (divisors n).

Lemma divpairs_sum : forall n, (1 <= n)%nat -> Rlsum (map w (divpairs n)) = INR (taun n) * rr n.
Proof.
  intros n Hn; unfold divpairs; rewrite map_map.
  rewrite (Rlsum_const (fun d => w (d, (n / d)%nat)) (divisors n) (rr n)).
  - unfold taun; reflexivity.
  - intros d Hd; apply in_divisors in Hd; destruct Hd as [[Hd1 _] Hmod].
    unfold w; cbn [fst snd].
    rewrite <- rr_mul; f_equal.
    apply Nat.Lcm0.mod_divide in Hmod; destruct Hmod as [c Hc]; subst n.
    rewrite Nat.div_mul by lia; ring.
Qed.

(* a NoDup-flat_map helper: disjoint blocks of NoDup lists give NoDup *)
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

Lemma pairbox_perm : forall N, Permutation (pairbox N) (flat_map divpairs (seq 1 N)).
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
      (* x = (d1, n1/d1) = (d2, n2/d2); d1=d2, n1/d1=n2/d2, d1|n1, d2|n2 => n1=n2 *)
      rewrite <- He1 in He2; injection He2 as Hf Hs.
      destruct Hm1 as [c1 Hc1]; destruct Hm2 as [c2 Hc2]; subst n1 n2.
      rewrite (Nat.div_mul c1 d1) in Hs by lia;
        rewrite (Nat.div_mul c2 d2) in Hs by lia.
      subst; nia.
  - intro ab; destruct ab as [a b]; split.
    + unfold pairbox; rewrite filter_In; intros [Hin Hle].
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
      unfold pairbox; apply filter_In; split.
      * apply in_prod; apply in_seq; nia.
      * apply Nat.leb_le; cbn [fst snd]; nia.
Qed.

Lemma Spart_eq_Dpart : forall N, Spart N = Dpart N.
Proof.
  intro N; unfold Spart, Dpart.
  rewrite (Rlsum_perm _ _ (Permutation_map w (pairbox_perm N))).
  rewrite Rlsum_map_flat_map.
  f_equal; apply map_ext_in; intros n Hn; apply in_seq in Hn; apply divpairs_sum; lia.
Qed.

Theorem zeta_two_sq_tau : Un_cv Dpart (Lz * Lz).
Proof.
  apply (Un_cv_eventually_eq Dpart Spart (Lz * Lz) 0).
  - intros N _; symmetry; apply Spart_eq_Dpart.
  - apply zeta_two_sq_hyperbola.
Qed.

(* ================================================================= *)
(*  Umbrella                                                          *)
(* ================================================================= *)
Theorem zeta_square_analytic :
  Un_cv Spart (Lz * Lz) /\
  (forall N, Spart N = Dpart N) /\
  Un_cv Dpart (Lz * Lz).
Proof. exact (conj zeta_two_sq_hyperbola (conj Spart_eq_Dpart zeta_two_sq_tau)). Qed.

Print Assumptions zeta_square_analytic.

(* ================================================================= *)
(*  END ZetaSquareAnalytic.v                                         *)
(*  ∑_{n≤N} τ(n)/n²  →  ζ(2)²  (= (proj1_sig zeta2_converges)²),      *)
(*  by the hyperbola squeeze over the ζ(2) arc.  Rests on the         *)
(*  classical Reals axioms (quarantined) — NOT axiom-free.           *)
(* ================================================================= *)
