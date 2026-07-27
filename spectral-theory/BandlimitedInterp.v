(* ================================================================= *)
(*  BandlimitedInterp.v  —  THE ALGEBRAIC NYQUIST–SHANNON BRIDGE.     *)
(*                                                                    *)
(*  The honest discrete→continuous sampling theorem over ℚ, the       *)
(*  algebraic incarnation of Shannon–Nyquist:                        *)
(*                                                                    *)
(*      bandwidth  =  polynomial degree bound.                       *)
(*                                                                    *)
(*  A signal that is "band-limited to bandwidth N" is a polynomial of *)
(*  degree < N (a `qdegle p (N-1)`).  This file proves the two halves *)
(*  of the sampling principle for such signals, with the CONTINUUM    *)
(*  being the full evaluation domain ℚ (every x : Qc), reconstructed  *)
(*  from finitely many samples:                                      *)
(*                                                                    *)
(*    • sampling_unique  (ANTI-ALIASING / uniqueness): two band-      *)
(*        limited signals that agree at more sample nodes than the    *)
(*        bandwidth agree EVERYWHERE — the discrete samples pin the   *)
(*        whole continuous function.  (Directly from the ℚ[X]         *)
(*        polynomial identity theorem `QPolyPIT.poly_roots_eval`.)    *)
(*    • sampling_reconstruct  (RECONSTRUCTION / existence): for any   *)
(*        distinct nodes and any prescribed sample values there IS a  *)
(*        band-limited signal hitting them — built by an explicit     *)
(*        Newton incremental interpolant.                            *)
(*    • nyquist_sampling  bundles both; sampling_alias is the         *)
(*        contrapositive (distinct band-limited signals must differ   *)
(*        on some node inside any window of ≥ bandwidth samples).     *)
(*                                                                    *)
(*  This is the algebraic SIBLING of the trigonometric sampling       *)
(*  theorem (WalshSampling.v does the finite F₂³ Fourier instance):   *)
(*  the number of samples equals the bandwidth, undersampling aliases,*)
(*  and finite discrete data determines a function on a continuum.    *)
(*  It needs NO trigonometry, NO improper integral, NO L² — so it     *)
(*  lands BELOW the classical-ℝ quarantine wall.  Built entirely on   *)
(*  the axiom-free ℚ[X] tower (QPoly/QPolyDiv/QPolyPIT over `Qc`), so  *)
(*  `Print Assumptions` = Closed under the global context.           *)
(*                                                                    *)
(*  HONEST SCOPE: this is the ALGEBRAIC (polynomial-degree) Nyquist.  *)
(*  The genuine TRIGONOMETRIC Nyquist on T = ℝ/ℤ (band-limited =      *)
(*  Fourier support in [−N,N]) needs a constructive Fourier analysis  *)
(*  over ℝ (constructive trig, improper integrals, L²) that this      *)
(*  stdlib-only repo does not build.  The continuum here is ℚ (dense, *)
(*  the axiom-free real substrate), not the completed ℝ.             *)
(* ================================================================= *)

From Stdlib Require Import QArith Qcanon List Lia Arith.
Import ListNotations.
Require Import QPoly QPolyDiv QPolyMul QPolyRoot QPolyPIT.
Open Scope Qc_scope.

(* ----------------------------------------------------------------- *)
(*  Degree of a difference: subtracting two degree-≤n polys stays ≤n. *)
(* ----------------------------------------------------------------- *)
Lemma qdegle_qsub : forall p q n, qdegle p n -> qdegle q n -> qdegle (qsub p q) n.
Proof.
  intros p q n Hp Hq i Hi.
  rewrite qcoeff_sub, (Hp i Hi), (Hq i Hi); ring.
Qed.

(* ================================================================= *)
(*  PART 1 — ANTI-ALIASING (uniqueness).                             *)
(*  A band-limited signal is determined everywhere by more samples    *)
(*  than its bandwidth.  This IS the Nyquist criterion: #samples must  *)
(*  exceed the degree, else two distinct signals alias.              *)
(* ================================================================= *)
Theorem sampling_unique : forall n p q (pts : list Qc),
  qdegle p n -> qdegle q n ->
  NoDup pts -> (n < length pts)%nat ->
  (forall a, In a pts -> qeval p a = qeval q a) ->
  forall x, qeval p x = qeval q x.
Proof.
  intros n p q pts Hp Hq Hnd Hlen Hsamp x.
  assert (Hzero : forall y, qeval (qsub p q) y = 0).
  { apply (poly_roots_eval n (qsub p q) (qdegle_qsub p q n Hp Hq) pts Hnd Hlen).
    intros a Ha; rewrite qeval_sub, (Hsamp a Ha); ring. }
  pose proof (Hzero x) as Hx; rewrite qeval_sub in Hx.
  (* qeval p x - qeval q x = 0 → qeval p x = qeval q x *)
  replace (qeval p x) with (qeval p x - qeval q x + qeval q x) by ring.
  rewrite Hx; ring.
Qed.

(* Contrapositive (ANTI-ALIASING witness): two band-limited signals that
   differ somewhere on the continuum must already DISAGREE at some sample
   node — so undersampling below the bandwidth would alias.  Constructive:
   ℚ has decidable equality, so the offending node is found by finite
   search (`Forall_Exists_dec`), no classical logic. *)
Corollary sampling_alias : forall n p q (pts : list Qc),
  qdegle p n -> qdegle q n ->
  NoDup pts -> (n < length pts)%nat ->
  (exists x, qeval p x <> qeval q x) ->
  Exists (fun a => qeval p a <> qeval q a) pts.
Proof.
  intros n p q pts Hp Hq Hnd Hlen [x Hx].
  destruct (Forall_Exists_dec (fun a => qeval p a = qeval q a)
              (fun a => Qc_eq_dec (qeval p a) (qeval q a)) pts) as [Hall | Hex].
  - exfalso; apply Hx.
    apply (sampling_unique n p q pts Hp Hq Hnd Hlen).
    intros a Ha; rewrite Forall_forall in Hall; apply Hall; exact Ha.
  - exact Hex.
Qed.

(* ================================================================= *)
(*  PART 2 — RECONSTRUCTION (existence): the Newton interpolant.      *)
(* ================================================================= *)

(* the linear node factor  X − a *)
Definition pfac (a : Qc) : qpoly := [Qcopp a; 1].
Lemma qeval_pfac : forall a x, qeval (pfac a) x = x - a.
Proof. intros a x; simpl; ring. Qed.
Lemma qdegle_pfac : forall a, qdegle (pfac a) 1.
Proof. intros a i Hi; unfold qcoeff; apply nth_overflow; simpl; lia. Qed.

(* the product of node factors ∏_{a∈pts} (X − a) *)
Fixpoint pprod (pts : list Qc) : qpoly :=
  match pts with
  | [] => [1]
  | a :: rest => qmul (pfac a) (pprod rest)
  end.

Lemma qeval_pprod_nil : forall x, qeval (pprod []) x = 1.
Proof. intro x; cbn [pprod qeval]; ring. Qed.

Lemma qeval_pprod_cons : forall a rest x,
  qeval (pprod (a :: rest)) x = (x - a) * qeval (pprod rest) x.
Proof. intros a rest x; cbn [pprod]; rewrite qeval_mul, qeval_pfac; reflexivity. Qed.

Lemma qdegle_pprod : forall pts, qdegle (pprod pts) (length pts).
Proof.
  induction pts as [|a rest IH]; cbn [pprod length].
  - intros i Hi; unfold qcoeff; apply nth_overflow; simpl; lia.
  - change (S (length rest)) with (1 + length rest)%nat.
    apply qdegle_qmul; [ apply qdegle_pfac | exact IH ].
Qed.

(* the product vanishes at each of its nodes *)
Lemma pprod_root : forall pts a, In a pts -> qeval (pprod pts) a = 0.
Proof.
  induction pts as [|b rest IH]; intros a Hin; [ inversion Hin | ].
  rewrite qeval_pprod_cons; destruct Hin as [Hab | Hin].
  - subst b; replace (a - a) with (0:Qc) by ring; ring.
  - rewrite (IH a Hin); ring.
Qed.

(* off its nodes it is nonzero *)
Lemma pprod_ne : forall pts a, ~ In a pts -> qeval (pprod pts) a <> 0.
Proof.
  induction pts as [|b rest IH]; intros a Hni.
  - rewrite qeval_pprod_nil; exact qc_one_neq_zero.
  - rewrite qeval_pprod_cons.
    apply not_in_cons in Hni; destruct Hni as [Hab Hrest].
    intro Hmul; apply Qcmult_integral in Hmul; destruct Hmul as [H0 | H0].
    + apply Hab; symmetry.
      (* a − b = 0 → a = b *)
      replace b with (a - (a - b)) by ring; rewrite H0; ring.
    + exact (IH a Hrest H0).
Qed.

(* the Newton incremental interpolant for nodes `pts` and samples `f` *)
Fixpoint newton (pts : list Qc) (f : Qc -> Qc) : qpoly :=
  match pts with
  | [] => []
  | a :: rest =>
      let p := newton rest f in
      let c := (f a - qeval p a) * / (qeval (pprod rest) a) in
      qadd p (qscale c (pprod rest))
  end.

(* sharp degree bound: N nodes ⟹ degree ≤ N−1 (bandwidth = #samples) *)
Lemma newton_degle : forall pts f, qdegle (newton pts f) (Nat.pred (length pts)).
Proof.
  induction pts as [|a rest IH]; intros f; cbn [newton length].
  - intros i Hi; unfold qcoeff; apply nth_overflow; simpl; lia.
  - simpl Nat.pred; apply qdegle_add.
    + apply (qdegle_mono _ (Nat.pred (length rest))); [ apply IH | lia ].
    + apply qdegle_scale, qdegle_pprod.
Qed.

Theorem newton_interpolates : forall pts f, NoDup pts ->
  forall a, In a pts -> qeval (newton pts f) a = f a.
Proof.
  induction pts as [|b rest IH]; intros f Hnd a Hin; [ inversion Hin | ].
  apply NoDup_cons_iff in Hnd; destruct Hnd as [Hbr Hndr].
  cbn [newton]; rewrite qeval_add, qeval_scale.
  set (p := newton rest f) in *.
  destruct Hin as [Hab | Hin].
  - (* a = b : the head node — the correction term is tuned to hit f b *)
    subst b.
    assert (HD : qeval (pprod rest) a <> 0) by (apply pprod_ne; exact Hbr).
    rewrite <- Qcmult_assoc, (Qcmult_inv_l _ HD), Qcmult_1_r; ring.
  - (* a ∈ rest : the correction term vanishes there, IH finishes *)
    rewrite (pprod_root rest a Hin), Qcmult_0_r, Qcplus_0_r.
    apply IH; [ exact Hndr | exact Hin ].
Qed.

(* RECONSTRUCTION: distinct nodes + prescribed samples ⟹ a band-limited
   signal (degree < #nodes) hitting every sample. *)
Theorem sampling_reconstruct : forall (pts : list Qc) (f : Qc -> Qc),
  NoDup pts ->
  exists p, qdegle p (Nat.pred (length pts)) /\
            (forall a, In a pts -> qeval p a = f a).
Proof.
  intros pts f Hnd; exists (newton pts f); split.
  - apply newton_degle.
  - apply newton_interpolates; exact Hnd.
Qed.

(* ================================================================= *)
(*  PART 3 — THE BRIDGE THEOREM.                                     *)
(*  Existence ∧ uniqueness: a band-limited signal (degree < N) is     *)
(*  reconstructed from, and pinned by, any N distinct samples.        *)
(* ================================================================= *)
Theorem nyquist_sampling : forall (N : nat) (pts : list Qc),
  NoDup pts -> length pts = N -> (0 < N)%nat ->
  (* (existence) every prescribed sampling admits a band-limited signal *)
  (forall f : Qc -> Qc,
     exists p, qdegle p (Nat.pred N) /\ (forall a, In a pts -> qeval p a = f a))
  /\
  (* (uniqueness) two band-limited signals agreeing on the N samples
     agree on the whole continuum ℚ *)
  (forall p q, qdegle p (Nat.pred N) -> qdegle q (Nat.pred N) ->
     (forall a, In a pts -> qeval p a = qeval q a) ->
     forall x, qeval p x = qeval q x).
Proof.
  intros N pts Hnd Hlen HN; split.
  - intros f; rewrite <- Hlen; apply sampling_reconstruct; exact Hnd.
  - intros p q Hp Hq Hsamp x.
    apply (sampling_unique (Nat.pred N) p q pts Hp Hq Hnd); [ lia | exact Hsamp ].
Qed.

Print Assumptions nyquist_sampling.

(* ================================================================= *)
(*  END BandlimitedInterp.v                                          *)
(*  The algebraic Nyquist–Shannon bridge over ℚ: bandwidth = degree,  *)
(*  #samples = bandwidth, exact reconstruction (Newton interpolant)   *)
(*  and anti-aliasing (ℚ[X] identity theorem).  A genuine discrete→   *)
(*  continuous sampling theorem BELOW the classical-ℝ quarantine.     *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
