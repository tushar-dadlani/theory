(* ================================================================= *)
(*  ArchimedeanConcrete.v  —  the primorial archimedean tower as a     *)
(*  CONCRETE convergent sequence.                                     *)
(*                                                                    *)
(*  ArchimedeanCompletion.archimedean_recon_climit had to quantify     *)
(*  over "any sequence realising the reconstruction", because the      *)
(*  factorisation was only an existence (code_surj : Prop).            *)
(*  PadicValuation now gives the factorisation as a FUNCTION           *)
(*  (peel, with code ps (peel ps m) = m), so the reconstruction is a   *)
(*  genuine sequence                                                  *)
(*                                                                    *)
(*     recon n B := / fabs (primes_upto B) (peel (primes_upto B) n),  *)
(*                                                                    *)
(*  and it converges in CReal to the archimedean value:               *)
(*                                                                    *)
(*     recon_climit : cvQ (recon n) (inject_Q (inject_Z n)).          *)
(*                                                                    *)
(*  The "any realising sequence" quantifier is discharged by a single  *)
(*  canonical, computable tower.  Axiom-free (CReal completion).       *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs.
Require Import PrimeFactorizationN PrimeFactorizationExists PrimonGas
        ProductFormulaQ ArchimedeanTower ArchimedeanCompletion PadicValuation CRealCv.
From Stdlib Require Import ZArith Znumtheory QArith Qabs Lqa Lia List.
Import ListNotations.
Open Scope Q_scope.

(* the canonical, computable primorial reconstruction of |n|_∞ *)
Definition recon (n : Z) (B : nat) : Q :=
  / fabs (primes_upto B) (peel (primes_upto B) n).

Theorem recon_climit : forall n, (0 < n)%Z -> cvQ (recon n) (inject_Q (inject_Z n)).
Proof.
  intros n Hn; apply (archimedean_recon_climit (recon n) n Hn).
  intros B HB.
  assert (HBn : (n <= Z.of_nat B)%Z) by lia.
  exists (peel (primes_upto B) n).
  split; [ apply primes_upto_Forall | ].
  split; [ symmetry; apply peel_length | ].
  split.
  - apply peel_code;
      [ apply primes_upto_Forall | apply primes_upto_nodup | exact Hn | ].
    intros q Hq Hqn; apply primes_upto_complete; [ exact Hq | ].
    apply Z.le_trans with n; [ apply Z.divide_pos_le; [ exact Hn | exact Hqn ] | exact HBn ].
  - unfold recon; reflexivity.
Qed.

Print Assumptions recon_climit.

(* ================================================================= *)
(*  END ArchimedeanConcrete.v                                        *)
(*  recon n : nat -> Q is the concrete primorial reconstruction of     *)
(*  |n|_∞, and it converges in CReal to inject_Q (inject_Z n).  The     *)
(*  archimedean place is now, end to end, the limit of ONE explicit,    *)
(*  computable tower over the primorial lattice.                      *)
(* ================================================================= *)
