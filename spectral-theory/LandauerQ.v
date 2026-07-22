(* ================================================================= *)
(*  LandauerQ.v                                                       *)
(*                                                                    *)
(*  Erasing an involution's residue dissipates heat -- over Q, the    *)
(*  axiom-free rational version of Landauer.v, built on               *)
(*  WalshHadamardHilbertQ + InvolutionQ.  Print Assumptions reports    *)
(*  Closed under the global context (no Reals axioms).                *)
(*                                                                    *)
(*  "Heat" here is the rational L^2 energy; the residue is an exact    *)
(*  1/2-eigen-sector of the lazy bit-flip diffusion, and erasing it    *)
(*  costs (3/4)||res||^2 -- > 0 unless the residue was already zero.   *)
(* ================================================================= *)

From Stdlib Require Import QArith Lqa Bool.
Require Import WalshHadamardHilbertQ.
Require Import InvolutionQ.
Open Scope Q_scope.

(* the two single-bit-flip directions on the square *)
Definition e0 : Sq := mkSq true  false.
Definition e1 : Sq := mkSq false true.

(* the lazy bit-flip diffusion (matches Rop's space) *)
Definition heatstep (f : Sig) : Sig :=
  fun x => (1 # 2) * f x + (1 # 4) * (f (xorS x e0) + f (xorS x e1)).

(* dissipated heat = lost L^2 energy in one step *)
Definition heat_dissipated (g : Sig) : Q :=
  innerQ g g - innerQ (heatstep g) (heatstep g).

(* e0 + e1 = DS, so the two neighbours are Rop-conjugate *)
Lemma flip_relation : forall x, xorS x e1 = xorS DS (xorS x e0).
Proof. intros [a b]; destruct a, b; reflexivity. Qed.

(* the residue contracts by exactly 1/2 per heat step *)
Theorem stepQ_residue : forall f x, heatstep (antiQ f) x == (1 # 2) * antiQ f x.
Proof.
  intros f x; unfold heatstep.
  assert (H : antiQ f (xorS x e1) == - antiQ f (xorS x e0)).
  { rewrite flip_relation. exact (anti_neg f (xorS x e0)). }
  rewrite H; ring.
Qed.

(* erasing the residue dissipates 3/4 of its energy *)
Theorem residue_dissipation : forall f,
  heat_dissipated (antiQ f) == (3 # 4) * innerQ (antiQ f) (antiQ f).
Proof.
  intro f; unfold heat_dissipated.
  assert (Hs : innerQ (heatstep (antiQ f)) (heatstep (antiQ f))
               == (1 # 4) * innerQ (antiQ f) (antiQ f)).
  { transitivity (innerQ (fun c => (1 # 2) * antiQ f c)
                         (fun c => (1 # 2) * antiQ f c)).
    - apply innerQ_congr; intro c; exact (stepQ_residue f c).
    - rewrite (innerQ_scale2 (1 # 2) (1 # 2) (antiQ f) (antiQ f)); ring. }
  rewrite Hs; ring.
Qed.

Theorem dissipation_nonneg : forall f, 0 <= heat_dissipated (antiQ f).
Proof.
  intro f; rewrite residue_dissipation.
  pose proof (innerQ_pos (antiQ f)); nra.
Qed.

(* Landauer: a nonzero residue costs strictly positive dissipated heat *)
Theorem landauer : forall f,
  (exists c, ~ antiQ f c == 0) -> 0 < heat_dissipated (antiQ f).
Proof.
  intros f [c Hc]; rewrite residue_dissipation.
  assert (Hpos : 0 < innerQ (antiQ f) (antiQ f)).
  { destruct (Qlt_le_dec 0 (innerQ (antiQ f) (antiQ f))) as [H | H]; [ exact H | ].
    exfalso.
    assert (Hz : innerQ (antiQ f) (antiQ f) == 0)
      by (apply Qle_antisym; [ exact H | apply innerQ_pos ]).
    destruct (innerQ_definite (antiQ f) Hz) as [Z0 [Zr [Zi Zd]]].
    destruct c as [b0 b1]; destruct b0, b1;
      [ apply Hc; exact Zd | apply Hc; exact Zi
      | apply Hc; exact Zr | apply Hc; exact Z0 ]. }
  nra.
Qed.

(* zero cost exactly when there was nothing to erase (f already fixed) *)
Theorem free_iff_no_residue : forall f,
  heat_dissipated (antiQ f) == 0 <-> (forall c, Rop f c == f c).
Proof.
  intro f; rewrite residue_dissipation; split.
  - intro H.
    assert (H0 : innerQ (antiQ f) (antiQ f) == 0) by lra.
    apply (proj1 (anti_zero_iff_fixed f)).
    destruct (innerQ_definite (antiQ f) H0) as [Z0 [Zr [Zi Zd]]].
    intro c; destruct c as [b0 b1]; destruct b0, b1; assumption.
  - intro H.
    assert (Hz : forall c, antiQ f c == 0)
      by (apply (proj2 (anti_zero_iff_fixed f)); exact H).
    assert (H1 : innerQ (antiQ f) (antiQ f) == 0).
    { unfold innerQ; rewrite (Hz ZS), (Hz RS), (Hz IS), (Hz DS); ring. }
    rewrite H1; ring.
Qed.

(* ----------------------------------------------------------------- *)
(* MASTER THEOREM — over Q, axiom-free                               *)
(* ----------------------------------------------------------------- *)

Theorem no_involution_is_free_thermo :
  (forall f, heat_dissipated (antiQ f) == (3 # 4) * innerQ (antiQ f) (antiQ f))
  /\ (forall f, 0 <= heat_dissipated (antiQ f))
  /\ (forall f, (exists c, ~ antiQ f c == 0) -> 0 < heat_dissipated (antiQ f))
  /\ (forall f, heat_dissipated (antiQ f) == 0 <-> (forall c, Rop f c == f c)).
Proof.
  split; [ exact residue_dissipation | ].
  split; [ exact dissipation_nonneg | ].
  split; [ exact landauer | exact free_iff_no_residue ].
Qed.

Print Assumptions no_involution_is_free_thermo.

(* ================================================================= *)
(*  END LandauerQ.v — residue erasure dissipates, over Q, no axioms.  *)
(* ================================================================= *)
