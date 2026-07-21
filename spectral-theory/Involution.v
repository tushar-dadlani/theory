(* ================================================================= *)
(*  Involution.v                                                      *)
(*                                                                    *)
(*  "NO INVOLUTION IS FREE" -- the honest, provable form.             *)
(*                                                                    *)
(*  A reversible (orthogonal) involution R is, by itself, lossless    *)
(*  (WalshHadamardHilbert.Rop_orthogonal proves <Rf,Rg> = <f,g>).     *)
(*  So it is NOT true that an involution "costs" something in the     *)
(*  reversible sense -- that would contradict theorems already here.  *)
(*                                                                    *)
(*  What IS true is the RESIDUE DECOMPOSITION.  Any signal splits as  *)
(*     f = sym f  +  anti f,                                          *)
(*  where                                                             *)
(*     sym  f = (f + R f)/2   is R-FIXED     (the "free" part),        *)
(*     anti f = (f - R f)/2   is R-NEGATED   (the RESIDUE).            *)
(*  The residue is 0 exactly on the fixed points; a non-identity      *)
(*  involution therefore always leaves a nonzero residue on some      *)
(*  input.  The residue lives in the -1 eigenspace -- the             *)
(*  antisymmetric / antinode / transient sector -- orthogonal to the  *)
(*  conserved symmetric part, and it is precisely what a diffusion     *)
(*  dissipates (HeatFlow's decaying modes).                           *)
(*                                                                    *)
(*  So: the involution itself is free, but its RESIDUE is the seed of  *)
(*  the diffusion.  "Residue or diffusion" -- the residue is what      *)
(*  flows.  The standing-wave amplitude is a PURE residue.            *)
(*                                                                    *)
(*  We use the concrete reflection R = Rop (xor by DIAG) on the        *)
(*  observer square; standard Reals axioms only, no admit.            *)
(* ================================================================= *)

Require Import WalshHadamardHilbert.
Require Import StandingWaveSpectrum.
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the free (symmetric) part and the residue (antisymmetric part) *)
Definition sym  (f : RSig) : RSig := fun c => / 2 * (f c + Rop f c).
Definition anti (f : RSig) : RSig := fun c => / 2 * (f c - Rop f c).

(* ----------------------------------------------------------------- *)
(* The decomposition f = free + residue                              *)
(* ----------------------------------------------------------------- *)

Lemma decompose : forall f c, f c = sym f c + anti f c.
Proof. intros f c; unfold sym, anti; lra. Qed.

(* the apex reflection is a genuine involution on the square *)
Lemma xorqDIAG_inv : forall c, xorq DIAG (xorq DIAG c) = c.
Proof. intros [b0 b1]; destruct b0, b1; reflexivity. Qed.

(* the free part is fixed by the involution (conserved) *)
Lemma sym_fixed : forall f c, Rop (sym f) c = sym f c.
Proof. intros f c; unfold sym, Rop; rewrite xorqDIAG_inv; lra. Qed.

(* the residue is negated by the involution (a -1 eigenvector) *)
Lemma anti_neg : forall f c, Rop (anti f) c = - anti f c.
Proof. intros f c; unfold anti, Rop; rewrite xorqDIAG_inv; lra. Qed.

(* residue vanishes exactly on the fixed points *)
Lemma anti_zero_iff_fixed : forall f,
  (forall c, anti f c = 0) <-> (forall c, Rop f c = f c).
Proof.
  intro f; split.
  - intros H c; specialize (H c); unfold anti in H; lra.
  - intros H c; unfold anti; rewrite (H c); lra.
Qed.

(* free part _|_ residue: the two sectors are orthogonal *)
Lemma sym_anti_orthogonal : forall f, innerR (sym f) (anti f) = 0.
Proof.
  intro f; apply (eigenspaces_orthogonal (sym f) (anti f)).
  - exact (sym_fixed f).
  - exact (anti_neg f).
Qed.

(* ----------------------------------------------------------------- *)
(* The involution is NOT free: it leaves a residue                   *)
(* ----------------------------------------------------------------- *)

(* the standing-wave amplitude is a PURE residue (its own antipart) *)
Lemma amplitude_is_pure_residue : forall c, anti ampR c = ampR c.
Proof. intro c; unfold anti; rewrite (ampR_eigen c); lra. Qed.

(* hence the reflection does not act as the identity everywhere:       *)
(* some input carries a nonzero residue. *)
Theorem not_globally_free : ~ (forall f c, anti f c = 0).
Proof.
  intro H; specialize (H ampR ZERO).
  rewrite (amplitude_is_pure_residue ZERO) in H.
  destruct ampR_values as [H0 _]; rewrite H0 in H; lra.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — the residue principle                            *)
(* ----------------------------------------------------------------- *)

Theorem no_involution_is_free :
  (* every signal = its free (symmetric) part + its residue *)
  (forall f c, f c = sym f c + anti f c)
  (* the free part is conserved by the involution ... *)
  /\ (forall f c, Rop (sym f) c = sym f c)
  (* ... and the residue is negated (a -1 eigenvector) *)
  /\ (forall f c, Rop (anti f) c = - anti f c)
  (* free _|_ residue *)
  /\ (forall f, innerR (sym f) (anti f) = 0)
  (* the residue vanishes exactly on the fixed points *)
  /\ (forall f, (forall c, anti f c = 0) <-> (forall c, Rop f c = f c))
  (* and the involution is NOT globally free -- it leaves a residue *)
  /\ ~ (forall f c, anti f c = 0).
Proof.
  split; [ exact decompose | ].
  split; [ exact sym_fixed | ].
  split; [ exact anti_neg | ].
  split; [ exact sym_anti_orthogonal | ].
  split; [ exact anti_zero_iff_fixed | exact not_globally_free ].
Qed.

Print Assumptions no_involution_is_free.

(* ================================================================= *)
(*  END Involution.v                                                  *)
(*  An involution is free on its fixed (+1) sector and leaves a        *)
(*  residue on its (-1) sector; only the identity is residue-free.     *)
(*  The residue is the antisymmetric part a diffusion dissipates.      *)
(*  ZERO Admitted.                                                    *)
(* ================================================================= *)
