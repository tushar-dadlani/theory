(* ================================================================= *)
(*  ZetaArcConstructive.v                                           *)
(*                                                                    *)
(*  THE FULL AXIOM-FREE ζ(2) ARC — the constructive companion to the  *)
(*  quarantined `ZetaMaster`, now covering ALL FIVE movements over     *)
(*  Rocq's axiom-free constructive real `CReal` (with ζ(2) = the       *)
(*  limit `zeta2c`, no π²/6):                                          *)
(*                                                                    *)
(*    (I)   ζ(2)=Σ1/n² exists                 (zeta2c_cv)             *)
(*    (II)  finite Σ 1/mᵢ² ≤ ζ(2)             (recip_sq_le_zeta2c)    *)
(*    (III) Euler product ∏1/(1−p⁻²) → ζ(2)   (euler_product_...)     *)
(*    (IV)  the primorial-tower principle      (cvQ_tower)            *)
(*    (V)   ∑ τ(n)/n² → ζ(2)²                  (zeta_two_sq_tau_...)   *)
(*                                                                    *)
(*  `Print Assumptions zeta_arc_free` = Closed under the global       *)
(*  context.  Every movement of the classical `ZetaMaster.zeta_arc`   *)
(*  (which rests on the classical-ℝ axioms) is here reproved without   *)
(*  them.                                                             *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs
        Reals.Cauchy.ConstructiveRcomplete.
From Stdlib Require Import ZArith QArith Qabs Lqa Lia List Znumtheory.
Import ListNotations.
Require Import PrimonGas EulerReindex EulerProductZeta
        CRealCv ZetaConstructive ZetaSquareConstructive ZetaMasterConstructive
        EulerProductConstructive PrimorialTowerConstructive.
Local Open Scope Q_scope.

Theorem zeta_arc_free :
  (* (I) ζ(2) = Σ 1/n² exists as a constructive real *)
  cvQ zpartQ zeta2c /\
  (* (II) finite reciprocal-square sums are ≤ ζ(2) *)
  (forall L, NoDup L -> (forall m, In m L -> (1 <= m)%nat) ->
      (inject_Q (qsum (map qw L)) <= zeta2c)%CReal) /\
  (* (III) the Euler product ∏_{p≤N} 1/(1−p⁻²) → ζ(2) *)
  cvQ (fun N => ZfactorQ (primes_upto (S N))) zeta2c /\
  (* (IV) the primorial-tower principle: a monotone rung sequence ≤ ζ(2)
         eventually dominating the ζ(2) partials converges to ζ(2) *)
  (forall E : nat -> Q,
      (forall m n, (m <= n)%nat -> E m <= E n) ->
      (forall n, (inject_Q (E n) <= zeta2c)%CReal) ->
      (forall N, exists n, (zpartQ N <= E n)%Q) ->
      cvQ E zeta2c) /\
  (* (V) ∑ τ(n)/n² → ζ(2)² *)
  cvQ DpartQ (zeta2c * zeta2c)%CReal.
Proof.
  exact (conj zeta2c_cv
         (conj recip_sq_le_zeta2c
         (conj euler_product_constructive
         (conj cvQ_tower
               zeta_two_sq_tau_constructive)))).
Qed.

Print Assumptions zeta_arc_free.

(* ================================================================= *)
(*  END ZetaArcConstructive.v                                       *)
(*  All five movements of the ζ(2) arc, axiom-free on the             *)
(*  constructive real.  Closed under the global context.             *)
(* ================================================================= *)
