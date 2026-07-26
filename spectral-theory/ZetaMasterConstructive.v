(* ================================================================= *)
(*  ZetaMasterConstructive.v                                        *)
(*                                                                    *)
(*  MASTER umbrella for the AXIOM-FREE (constructive-`CReal`) ζ arc.  *)
(*                                                                    *)
(*  The classical `ZetaMaster.zeta_arc` bundles five movements over   *)
(*  the QUARANTINED classical ℝ.  This file bundles the movements     *)
(*  that have been rebuilt over Rocq's axiom-free constructive real   *)
(*  `CReal` (ZetaConstructive / ZetaSquareConstructive), plus a new    *)
(*  rational finite-sum bound:                                        *)
(*                                                                    *)
(*    (I)   ζ(2)=Σ1/n² exists as a CReal            (zeta2c_cv)       *)
(*    (II)  finite Σ 1/mᵢ² ≤ ζ(2)                    (recip_sq_le_...) *)
(*    (V)   ∑ τ(n)/n²  →  ζ(2)²                      (zeta_two_sq_...) *)
(*                                                                    *)
(*  Movement II is now the STRICT `≤ ζ(2)` form, via the monotone-    *)
(*  limit ε-principle `CRealCv.cvQ_term_le` (proved from ℚ-density,   *)
(*  `CRealQ_dense`).  `Print Assumptions zeta_arc_constructive` =      *)
(*  Closed under the global context.  Movements (III) the Euler        *)
(*  product and (IV) the primorial tower are NOT yet ported to         *)
(*  `CReal` (they remain only in the quarantined `ZetaMaster`).       *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import ZArith QArith Qabs Lqa Lia List Arith.
Import ListNotations.
Require Import PrimonGas CRealCv ZetaConstructive ZetaSquareConstructive.
Local Open Scope Q_scope.

(* ================================================================= *)
(*  Movement II — finite reciprocal-square sums (over ℚ)             *)
(*  A NoDup list of positive integers sums (of 1/m²) to at most the   *)
(*  ζ(2) partial sum SMQ (S (list_max L)).                            *)
(* ================================================================= *)
Lemma remove_nodup_nat : forall x l, NoDup l -> NoDup (remove Nat.eq_dec x l).
Proof.
  intros x l; induction l as [|a l IH]; intro Hnd; simpl; [ constructor | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  destruct (Nat.eq_dec x a) as [He | Hne]; [ apply IH; exact Hnd' | ].
  constructor;
    [ intro Hin; apply in_remove in Hin; destruct Hin as [Hin _]; contradiction
    | apply IH; exact Hnd' ].
Qed.

Lemma qsum_remove_qw : forall r l, In r l -> NoDup l ->
  qsum (map qw l) == qw r + qsum (map qw (remove Nat.eq_dec r l)).
Proof.
  intros r l; induction l as [|a l IH]; intros Hin Hnd; [ destruct Hin | ].
  inversion Hnd as [| ? ? Hnin Hnd']; subst.
  cbn [map remove]; destruct (Nat.eq_dec r a) as [He | Hne].
  - subst a; rewrite (notin_remove Nat.eq_dec l r Hnin); cbn [map qsum]; reflexivity.
  - destruct Hin as [Ha | Hin]; [ symmetry in Ha; contradiction | ].
    cbn [map qsum]; rewrite (IH Hin Hnd'); ring.
Qed.

Lemma qsum_incl_le_qw : forall Rs L,
  NoDup L -> incl L Rs -> qsum (map qw L) <= qsum (map qw Rs).
Proof.
  induction Rs as [|r R' IH]; intros L Hnd Hincl.
  - assert (L = []).
    { destruct L as [|a L0]; [ reflexivity | exfalso; destruct (Hincl a (in_eq a L0)) ]. }
    subst; simpl; apply Qle_refl.
  - cbn [map qsum]; destruct (in_dec Nat.eq_dec r L) as [Hin | Hnin].
    + rewrite (qsum_remove_qw r L Hin Hnd).
      apply Qplus_le_r, IH; [ apply remove_nodup_nat; exact Hnd | ].
      intros x Hx; apply in_remove in Hx; destruct Hx as [Hx1 Hx2].
      destruct (Hincl x Hx1) as [He | Hin'];
        [ exfalso; apply Hx2; symmetry; exact He | exact Hin' ].
    + apply Qle_trans with (qsum (map qw R')).
      * apply IH; [ exact Hnd | ].
        intros x Hx; destruct (Hincl x Hx) as [He | Hin'];
          [ subst r; contradiction | exact Hin' ].
      * pose proof (qw_nonneg r); lra.
Qed.

Theorem recip_sq_partial_bound : forall L,
  NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
  qsum (map qw L) <= SMQ (S (list_max L)).
Proof.
  intros L Hnd Hpos; unfold SMQ; apply qsum_incl_le_qw; [ exact Hnd | ].
  intros m Hm; apply in_seq.
  assert (Hle : (m <= list_max L)%nat).
  { apply (proj1 (Forall_forall _ _)
                 (proj1 (list_max_le L (list_max L)) (Nat.le_refl _)) m Hm). }
  split; [ apply Hpos; exact Hm | lia ].
Qed.

(* the ζ(2) partial sums are monotone, hence each is ≤ ζ(2) (via cvQ_term_le) *)
Lemma SMQ_mono : forall m n, (m <= n)%nat -> SMQ m <= SMQ n.
Proof.
  intros m n; induction n as [|n IH]; intro H.
  - assert (m = 0)%nat by lia; subst; apply Qle_refl.
  - destruct (Nat.eq_dec m (S n)) as [->|Hne]; [ apply Qle_refl | ].
    rewrite SMQ_S; apply Qle_trans with (SMQ n);
      [ apply IH; lia | pose proof (qw_nonneg (S n)); lra ].
Qed.

Lemma SMQ_le_zeta2c : forall M, (inject_Q (SMQ M) <= zeta2c)%CReal.
Proof. apply cvQ_term_le; [ apply SMQ_cv | apply SMQ_mono ]. Qed.

(* strict form of movement II:  finite Σ 1/mᵢ²  ≤  ζ(2) *)
Theorem recip_sq_le_zeta2c : forall L,
  NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
  (inject_Q (qsum (map qw L)) <= zeta2c)%CReal.
Proof.
  intros L Hnd Hpos.
  apply CReal_le_trans with (inject_Q (SMQ (S (list_max L)))).
  - apply inject_Q_le, recip_sq_partial_bound; assumption.
  - apply SMQ_le_zeta2c.
Qed.

(* ================================================================= *)
(*  THE UMBRELLA                                                      *)
(* ================================================================= *)
Theorem zeta_arc_constructive :
  (* (I) ζ(2) = Σ 1/n² exists as a constructive real *)
  cvQ zpartQ zeta2c /\
  (* (II) finite reciprocal-square sums are ≤ ζ(2) *)
  (forall L, NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
      (inject_Q (qsum (map qw L)) <= zeta2c)%CReal) /\
  (* the hyperbola sum converges to ζ(2)² and equals the τ Dirichlet sum *)
  cvQ SpartQ (zeta2c * zeta2c)%CReal /\
  (forall N, SpartQ N == DpartQ N) /\
  (* (V) ∑ τ(n)/n²  →  ζ(2)² *)
  cvQ DpartQ (zeta2c * zeta2c)%CReal.
Proof.
  exact (conj zeta2c_cv
         (conj recip_sq_le_zeta2c
         (conj SpartQ_cv
         (conj Spart_eq_Dpart
               zeta_two_sq_tau_constructive)))).
Qed.

Print Assumptions zeta_arc_constructive.

(* ================================================================= *)
(*  END ZetaMasterConstructive.v                                    *)
(*  Axiom-free umbrella for the constructive ζ arc: ζ(2) as a CReal,  *)
(*  the finite reciprocal-square bound, and ∑τ(n)/n² = ζ(2)².         *)
(*  Closed under the global context.  (Euler product & primorial      *)
(*  tower over CReal, and the strict ≤ ζ(2) bound, remain to port.)   *)
(* ================================================================= *)
