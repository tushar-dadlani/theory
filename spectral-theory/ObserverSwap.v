(* ================================================================= *)
(*  ObserverSwap.v                                                   *)
(*                                                                    *)
(*  THE INVOLUTION COUSIN of ObserverTriad's measurement operator:     *)
(*  the observer<->observed SWAP S (fixing the observation).          *)
(*                                                                    *)
(*        [ 0 1 0 ]                                                   *)
(*    S = [ 1 0 0 ]   -- symmetric (self-adjoint) AND an involution    *)
(*        [ 0 0 1 ]      (S o S = I), so its spectrum is {+1, -1}.     *)
(*                                                                    *)
(*  This realises the 3-symbol algebra's unit group {I,N} ~= Z/2       *)
(*  (INFMonoid) as a reflection on the triad:                          *)
(*    - the antisymmetric mode  v0 = Observer - Observed  is NEGATED    *)
(*        (eigenvalue -1 = val N): S is the involution N;             *)
(*    - the symmetric modes  vs = Observer + Observed  and             *)
(*        von = Observation  are FIXED (eigenvalue +1 = val I).         *)
(*                                                                    *)
(*  The tie to ObserverTriad: v0 is BOTH the kernel of the measurement  *)
(*  M (invisible to observation, ObserverTriad.eig_0) AND the -1        *)
(*  eigenvector of the swap S -- the residue the measurement cannot     *)
(*  resolve is exactly what the observer/observed swap flips.  Plus the  *)
(*  reflection residue decomposition f = sym + anti (as in Involution). *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

Require Import ObserverTriad INFMonoid.
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the observer<->observed swap, fixing the observation *)
Definition S (f : State) : State :=
  fun r => match r with
           | Observer    => f Observed
           | Observed    => f Observer
           | Observation => f Observation
           end.

(* ----------------------------------------------------------------- *)
(*  SELF-ADJOINT and INVOLUTION                                       *)
(* ----------------------------------------------------------------- *)

Theorem S_self_adjoint : forall f g, inner (S f) g = inner f (S g).
Proof. intros f g; unfold inner, S; ring. Qed.

Theorem S_involution : forall f r, S (S f) r = f r.
Proof. intros f r; destruct r; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  SPECTRUM {+1, -1}                                                *)
(* ----------------------------------------------------------------- *)

Definition vs  : State := fun r => match r with Observation => 0 | _ => 1 end.
Definition von : State := fun r => match r with Observation => 1 | _ => 0 end.

(* the antisymmetric mode is negated (eigenvalue -1) *)
Theorem S_eig_v0 : forall r, S v0 r = smul (-1) v0 r.
Proof. intro r; destruct r; unfold S, v0, smul; ring. Qed.

(* the symmetric modes are fixed (eigenvalue +1) *)
Theorem S_eig_vs : forall r, S vs r = smul 1 vs r.
Proof. intro r; destruct r; unfold S, vs, smul; ring. Qed.

Theorem S_eig_von : forall r, S von r = smul 1 von r.
Proof. intro r; destruct r; unfold S, von, smul; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  ORTHOGONAL EIGENBASIS                                            *)
(* ----------------------------------------------------------------- *)

Theorem S_ortho_v0_vs  : inner v0 vs  = 0.  Proof. unfold inner, v0, vs;  ring. Qed.
Theorem S_ortho_v0_von : inner v0 von = 0.  Proof. unfold inner, v0, von; ring. Qed.
Theorem S_ortho_vs_von : inner vs von = 0.  Proof. unfold inner, vs, von; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  THE TIE TO {I,N,F}:  the +/-1 spectrum IS the unit group {I,N}    *)
(* ----------------------------------------------------------------- *)

Lemma IZR_val_N : IZR (val INFMonoid.N) = -1.  Proof. reflexivity. Qed.
Lemma IZR_val_I : IZR (val INFMonoid.I) = 1.   Proof. reflexivity. Qed.

(* v0 is the N-eigenmode of the swap (eigenvalue val N = -1) *)
Theorem v0_is_N_mode : forall r, S v0 r = smul (IZR (val INFMonoid.N)) v0 r.
Proof. intro r; rewrite IZR_val_N; apply S_eig_v0. Qed.

(* vs is an I-eigenmode of the swap (eigenvalue val I = +1) *)
Theorem vs_is_I_mode : forall r, S vs r = smul (IZR (val INFMonoid.I)) vs r.
Proof. intro r; rewrite IZR_val_I; apply S_eig_vs. Qed.

(* ----------------------------------------------------------------- *)
(*  THE TIE TO THE MEASUREMENT: v0 is invisible to M and flipped by S  *)
(* ----------------------------------------------------------------- *)

Theorem residue_mode : forall r, M v0 r = 0 /\ S v0 r = - v0 r.
Proof.
  intro r; split.
  - rewrite eig_0; unfold smul; ring.
  - rewrite S_eig_v0; unfold smul; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  REFLECTION RESIDUE DECOMPOSITION (cf. Involution.v)               *)
(* ----------------------------------------------------------------- *)

Definition sym_part  (f : State) : State := fun r => (f r + S f r) / 2.
Definition anti_part (f : State) : State := fun r => (f r - S f r) / 2.

Theorem decomposition : forall f r, f r = sym_part f r + anti_part f r.
Proof. intros f r; unfold sym_part, anti_part; field. Qed.

Theorem sym_fixed : forall f r, S (sym_part f) r = sym_part f r.
Proof. intros f r; destruct r; unfold sym_part; cbn [S]; field. Qed.

Theorem anti_negated : forall f r, S (anti_part f) r = smul (-1) (anti_part f) r.
Proof. intros f r; destruct r; unfold anti_part, smul; cbn [S]; field. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM                                                   *)
(* ----------------------------------------------------------------- *)

Theorem observer_swap_involution :
  (* self-adjoint involution (a reflection): spectrum {+1,-1} *)
  (forall f g, inner (S f) g = inner f (S g))
  /\ (forall f r, S (S f) r = f r)
  /\ (forall r, S v0 r = smul (-1) v0 r)          (* antisymmetric mode, -1 = val N *)
  /\ (forall r, S vs r = smul 1 vs r)             (* symmetric mode,    +1 = val I *)
  /\ (forall r, S von r = smul 1 von r)
  /\ inner v0 vs = 0 /\ inner v0 von = 0 /\ inner vs von = 0
  (* v0 is simultaneously the measurement kernel and the swap's -1 mode *)
  /\ (forall r, M v0 r = 0 /\ S v0 r = - v0 r)
  (* and the reflection splits every state into fixed + negated parts *)
  /\ (forall f r, f r = sym_part f r + anti_part f r).
Proof.
  split; [ exact S_self_adjoint | ].
  split; [ exact S_involution | ].
  split; [ exact S_eig_v0 | ].
  split; [ exact S_eig_vs | ].
  split; [ exact S_eig_von | ].
  split; [ exact S_ortho_v0_vs | ].
  split; [ exact S_ortho_v0_von | ].
  split; [ exact S_ortho_vs_von | ].
  split; [ exact residue_mode | exact decomposition ].
Qed.

Print Assumptions observer_swap_involution.

(* ================================================================= *)
(*  END ObserverSwap.v                                               *)
(*  The observer<->observed swap S: a self-adjoint involution whose     *)
(*  spectrum {+1,-1} realises the unit group {I,N} of the 3-symbol      *)
(*  algebra (val I, val N), with the -1 eigenmode v0 = Observer -        *)
(*  Observed being exactly the measurement kernel of ObserverTriad.M.   *)
(*  Uses the classical Reals axioms (quarantined).                     *)
(* ================================================================= *)
