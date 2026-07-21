(* ================================================================= *)
(*  Landauer.v                                                        *)
(*                                                                    *)
(*  THE LANDAUER BRIDGE: erasing an involution's residue dissipates.  *)
(*                                                                    *)
(*  A reversible involution (Rop) is free (WalshHadamardHilbert       *)
(*  proves it orthogonal).  The cost appears only when you ERASE the  *)
(*  residue it leaves -- i.e. couple it to the dissipative diffusion  *)
(*  and relax to equilibrium.  We model the diffusion on the observer *)
(*  square F_2^2 (the same space as Rop) as the lazy bit-flip walk    *)
(*     (stepQ f)(x) = 1/2 f(x) + 1/4 [f(x+e0) + f(x+e1)].             *)
(*                                                                    *)
(*  Key fact: the residue anti f is a -1 eigenvector of Rop = xor by  *)
(*  DIAG, and since e0 + e1 = DIAG, the two neighbours of the walk    *)
(*  are Rop-conjugate, so they CANCEL on the residue:                 *)
(*     stepQ (anti f) = 1/2 . anti f          (an exact 1/2-sector)   *)
(*  The residue therefore strictly contracts under the heat step.     *)
(*                                                                    *)
(*  Defining the dissipated "heat" as the lost L^2-energy             *)
(*     heat_dissipated g = <g,g> - <stepQ g, stepQ g>,                *)
(*  we prove (standard Reals axioms only; no admit):                  *)
(*     heat_dissipated (anti f) = 3/4 <anti f, anti f> >= 0,          *)
(*  which is > 0 exactly when the residue is nonzero, and = 0 exactly *)
(*  when f was already Rop-fixed (residue-free).                      *)
(*                                                                    *)
(*  HONEST SCOPE: "heat" here is the inner-product (L^2) energy, NOT   *)
(*  k T ln 2 -- there is no temperature/Boltzmann constant in the      *)
(*  model.  This is Landauer's STRUCTURE (irreversible erasure => a    *)
(*  strictly positive energy cost, zero only with nothing to erase),   *)
(*  not the physical constant.  The 3/4 is specific to this lazy       *)
(*  2-bit walk (residue eigenvalue 1/2).  The cost is charged to the   *)
(*  diffusion, not the (free) involution.                             *)
(* ================================================================= *)

Require Import Involution.
Require Import WalshHadamardHilbert.
Require Import StandingWaveSpectrum.
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the two single-bit-flip directions on the square *)
Definition e0 : Q := mkQ true  false.
Definition e1 : Q := mkQ false true.

(* the lazy bit-flip diffusion on the square (matches Rop's space) *)
Definition stepQ (f : RSig) : RSig :=
  fun x => / 2 * f x + / 4 * (f (xorq x e0) + f (xorq x e1)).

(* dissipated heat = lost L^2 energy in one step *)
Definition heat_dissipated (g : RSig) : R :=
  innerR g g - innerR (stepQ g) (stepQ g).

(* ----------------------------------------------------------------- *)
(* SECTION 1 — the residue is an exact 1/2-eigen-sector of the flow   *)
(* ----------------------------------------------------------------- *)

(* e0 + e1 = DIAG, so the two neighbours are Rop-conjugate *)
Lemma flip_relation : forall x, xorq x e1 = xorq DIAG (xorq x e0).
Proof. intros [a b]; destruct a, b; reflexivity. Qed.

(* the residue contracts by exactly 1/2 per heat step *)
Theorem stepQ_residue : forall f x, stepQ (anti f) x = / 2 * anti f x.
Proof.
  intros f x. unfold stepQ.
  assert (H : anti f (xorq x e1) = - anti f (xorq x e0)).
  { rewrite flip_relation. exact (anti_neg f (xorq x e0)). }
  rewrite H. lra.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 2 — the dissipation                                        *)
(* ----------------------------------------------------------------- *)

(* inner product scales quadratically under a common scalar *)
Lemma innerR_scale2 : forall a g,
  innerR (fun c => a * g c) (fun c => a * g c) = a * a * innerR g g.
Proof. intros a g; unfold innerR; cbn; ring. Qed.

(* erasing the residue dissipates 3/4 of its energy *)
Theorem residue_dissipation : forall f,
  heat_dissipated (anti f) = 3 / 4 * innerR (anti f) (anti f).
Proof.
  intro f; unfold heat_dissipated.
  assert (Hs : innerR (stepQ (anti f)) (stepQ (anti f))
               = / 4 * innerR (anti f) (anti f)).
  { transitivity (innerR (fun c => / 2 * anti f c) (fun c => / 2 * anti f c)).
    - apply innerR_congr; intro c; exact (stepQ_residue f c).
    - rewrite (innerR_scale2 (/ 2) (anti f)); lra. }
  rewrite Hs; lra.
Qed.

(* the dissipation is nonnegative *)
Theorem dissipation_nonneg : forall f, 0 <= heat_dissipated (anti f).
Proof.
  intro f; rewrite residue_dissipation.
  pose proof (innerR_pos (anti f)); lra.
Qed.

(* ----------------------------------------------------------------- *)
(* SECTION 3 — Landauer: nonzero residue => strictly positive cost    *)
(* ----------------------------------------------------------------- *)

Theorem landauer : forall f,
  (exists c, anti f c <> 0) -> heat_dissipated (anti f) > 0.
Proof.
  intros f [c Hc]; rewrite residue_dissipation.
  assert (Hpos : innerR (anti f) (anti f) > 0).
  { destruct (Rtotal_order (innerR (anti f) (anti f)) 0) as [H | [H | H]].
    - pose proof (innerR_pos (anti f)); lra.
    - exfalso.
      destruct (innerR_definite (anti f) H) as [Z0 [Zr [Zi Zd]]].
      destruct c as [b0 b1]; destruct b0, b1;
        [ exact (Hc Zd) | exact (Hc Zi) | exact (Hc Zr) | exact (Hc Z0) ].
    - exact H. }
  lra.
Qed.

(* zero cost exactly when there was nothing to erase (f already fixed) *)
Theorem free_iff_no_residue : forall f,
  heat_dissipated (anti f) = 0 <-> (forall c, Rop f c = f c).
Proof.
  intro f; rewrite residue_dissipation; split.
  - intro H.
    assert (H0 : innerR (anti f) (anti f) = 0) by lra.
    destruct (innerR_definite (anti f) H0) as [Z0 [Zr [Zi Zd]]].
    assert (Hz : forall c, anti f c = 0).
    { intro c; destruct c as [b0 b1]; destruct b0, b1; assumption. }
    exact (proj1 (anti_zero_iff_fixed f) Hz).
  - intro H.
    pose proof (proj2 (anti_zero_iff_fixed f) H) as Hz.
    assert (H1 : innerR (anti f) (anti f) = 0).
    { unfold innerR; rewrite (Hz ZERO), (Hz REAL), (Hz IMAG), (Hz DIAG); lra. }
    rewrite H1; lra.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — no involution is free (for the irreversible reset) *)
(* ----------------------------------------------------------------- *)

Theorem no_involution_is_free_thermo :
  (* erasing the residue dissipates 3/4 of its energy ... *)
  (forall f, heat_dissipated (anti f) = 3 / 4 * innerR (anti f) (anti f))
  (* ... which is always nonnegative, ... *)
  /\ (forall f, 0 <= heat_dissipated (anti f))
  (* ... strictly positive whenever the residue is nonzero, ... *)
  /\ (forall f, (exists c, anti f c <> 0) -> heat_dissipated (anti f) > 0)
  (* ... and zero exactly when f was already fixed (nothing to erase). *)
  /\ (forall f, heat_dissipated (anti f) = 0 <-> (forall c, Rop f c = f c)).
Proof.
  split; [ exact residue_dissipation | ].
  split; [ exact dissipation_nonneg | ].
  split; [ exact landauer | exact free_iff_no_residue ].
Qed.

Print Assumptions no_involution_is_free_thermo.

(* ================================================================= *)
(*  END Landauer.v                                                    *)
(*  Erasing a nontrivial involution's residue costs strictly positive *)
(*  dissipated energy; only a fixed point (residue-free) is free.      *)
(*  ZERO Admitted.                                                    *)
(* ================================================================= *)
