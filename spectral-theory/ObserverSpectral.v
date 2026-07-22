(* ================================================================= *)
(*  ObserverSpectral.v                                               *)
(*                                                                    *)
(*  COMMUTING OBSERVABLES on the observer/observed/observation triad:  *)
(*  the measurement M (ObserverTriad) and the observer<->observed swap *)
(*  S (ObserverSwap) COMMUTE, and are simultaneously diagonalised by    *)
(*  the single eigenbasis {v0, vp, vm}.                                *)
(*                                                                    *)
(*    MS_commute : M o S = S o M   ([M,S] = 0)                         *)
(*                                                                    *)
(*  and on the joint eigenbasis (ObserverTriad's M-eigenvectors, which  *)
(*  are ALSO S-eigenvectors):                                          *)
(*        vector            M-eigenvalue     S-eigenvalue              *)
(*        v0 = Or - Od          0               -1   (= val N)         *)
(*        vp = Or+Od+ sqrt2.On  +sqrt2          +1   (= val I)         *)
(*        vm = Or+Od- sqrt2.On  -sqrt2          +1   (= val I)         *)
(*                                                                    *)
(*  Two self-adjoint observables (a measurement and a symmetry) that    *)
(*  commute and share an orthogonal eigenbasis -- the finite spectral    *)
(*  picture of "simultaneously measurable" observables.  The shared      *)
(*  mode v0 = Observer - Observed is the measurement kernel AND the      *)
(*  swap's -1 eigenvector; the observable modes vp, vm are swap-fixed.   *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

Require Import ObserverTriad ObserverSwap.
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* the two observables commute *)
Theorem MS_commute : forall f r, M (S f) r = S (M f) r.
Proof. intros f r; destruct r; cbn [M S]; ring. Qed.

(* the M-eigenvectors vp, vm are also S-eigenvectors (eigenvalue +1) *)
Theorem S_eig_vp : forall r, S vp r = smul 1 vp r.
Proof. intro r; destruct r; unfold S, vp, smul; ring. Qed.

Theorem S_eig_vm : forall r, S vm r = smul 1 vm r.
Proof. intro r; destruct r; unfold S, vm, smul; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM: commuting observables, joint diagonalization      *)
(* ----------------------------------------------------------------- *)

Theorem commuting_observables :
  (* [M, S] = 0 *)
  (forall f r, M (S f) r = S (M f) r)
  (* {v0, vp, vm} simultaneously diagonalizes M and S *)
  /\ (forall r, M v0 r = smul 0 v0 r)          /\ (forall r, S v0 r = smul (-1) v0 r)
  /\ (forall r, M vp r = smul (sqrt 2) vp r)   /\ (forall r, S vp r = smul 1 vp r)
  /\ (forall r, M vm r = smul (- sqrt 2) vm r) /\ (forall r, S vm r = smul 1 vm r).
Proof.
  split; [ exact MS_commute | ].
  split; [ exact eig_0 | ].
  split; [ exact S_eig_v0 | ].
  split; [ exact eig_p | ].
  split; [ exact S_eig_vp | ].
  split; [ exact eig_m | exact S_eig_vm ].
Qed.

Print Assumptions commuting_observables.

(* ================================================================= *)
(*  END ObserverSpectral.v                                           *)
(*  The measurement M and the observer<->observed swap S are commuting  *)
(*  self-adjoint observables ([M,S]=0) with a joint orthogonal          *)
(*  eigenbasis {v0, vp, vm}: v0 (M-kernel / S(-1)) and vp, vm (M's        *)
(*  +/-sqrt2 modes, both S-fixed).  Uses the classical Reals axioms.    *)
(* ================================================================= *)
