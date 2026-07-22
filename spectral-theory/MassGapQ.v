(* ================================================================= *)
(*  MassGapQ.v                                                        *)
(*                                                                    *)
(*  The mu-energy bridge over Q -- the axiom-free rational version of  *)
(*  MassGap.v's one Reals-dependent part.  (MassGap's spectral_gap /   *)
(*  has_mass_gap results are already nat and axiom-free.)             *)
(*                                                                    *)
(*  Reading a Walsh mode's energy as its Hamming weight |y|, the       *)
(*  HeatFlowQ diffusion eigenvalue is  mu y = 1 - |y|/3, so the         *)
(*  vacuum (|y|=0) is stationary (mu=1) and the lightest excitation    *)
(*  (|y|=1) is the slowest transient (mu=2/3) -- all over Q.          *)
(* ================================================================= *)

Require Import HeatFlowQ.
Require Import WalshHadamard.
From Stdlib Require Import QArith Lqa Bool ZArith.
Open Scope Q_scope.

Definition weight (y : P3) : nat :=
  match y with
  | mkP a b c => (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
  end.

(* the diffusion eigenvalue is set by the energy |y| (= Hamming weight): *)
(* on the four shells |y| = 0,1,2,3 it takes the values 1 - |y|/3.      *)
Theorem mu_spectrum :
  mu (mkP false false false) == 1        (* |y| = 0 *)
  /\ mu (mkP true  false false) == 2 # 3  (* |y| = 1 *)
  /\ mu (mkP true  true  false) == 1 # 3  (* |y| = 2 *)
  /\ mu (mkP true  true  true)  == 0.     (* |y| = 3 *)
Proof.
  unfold mu, chrq, dot, e0, e1, e2, c0, c1, c2; cbn; repeat split; lra.
Qed.

(* vacuum: energy 0, stationary *)
Theorem vacuum_stationary : mu zero3 == 1.
Proof. exact mu_zero. Qed.

(* lightest excitation: energy 1, slowest transient (mu = 2/3) *)
Theorem lightest_excitation : mu e0 == 2 # 3 /\ weight e0 = 1%nat.
Proof.
  split; [ unfold mu, chrq, dot, e0, e1, e2, c0, c1, c2; cbn; lra | reflexivity ].
Qed.

Theorem massgapQ :
  (mu (mkP false false false) == 1
   /\ mu (mkP true false false) == 2 # 3
   /\ mu (mkP true true false) == 1 # 3
   /\ mu (mkP true true true) == 0)
  /\ mu zero3 == 1
  /\ mu e0 == 2 # 3
  /\ (forall y, y <> zero3 -> 0 <= mu y <= 2 # 3).
Proof.
  split; [ exact mu_spectrum | ].
  split; [ exact mu_zero | ].
  split; [ exact (proj1 lightest_excitation) | exact mu_bound ].
Qed.

Print Assumptions massgapQ.

(* ================================================================= *)
(*  END MassGapQ.v — the mu = 1 - |y|/3 energy bridge over Q.          *)
(* ================================================================= *)
