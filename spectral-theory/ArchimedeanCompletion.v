(* ================================================================= *)
(*  ArchimedeanCompletion.v  —  the primorial archimedean tower as a   *)
(*  CReal LIMIT (attaching the completion layer to ArchimedeanTower). *)
(*                                                                    *)
(*  ArchimedeanTower gives the reconstruction |n|_∞ = / fabs(primes_    *)
(*  upto B) at every primorial cutoff B ≥ n, STATIONARY in B.  Here we  *)
(*  strengthen that stationarity into a genuine limit in the           *)
(*  constructive reals: any rational sequence that realises the        *)
(*  primorial reconstruction converges (cvQ) to the CReal embedding    *)
(*  of the archimedean value.                                         *)
(*                                                                    *)
(*    cvQ_const              : the constant q converges to inject_Q q; *)
(*    archimedean_climit     : a sequence eventually = inject_Z n       *)
(*                             converges to inject_Q (inject_Z n);      *)
(*    archimedean_recon_climit: any sequence with a B == /fabs(...) for *)
(*                             B ≥ ⌊n⌋ (i.e. realising the reconstruc-  *)
(*                             tion) converges to inject_Q (inject_Z n);*)
(*    archimedean_place_climit: the stationary reconstruction value     *)
(*                             itself converges to |n|_∞ in CReal.      *)
(*                                                                    *)
(*  This is LAYER 2 (completion): the primorial lattice defines the    *)
(*  archimedean place (ArchimedeanTower, layer 1, zero axioms), and     *)
(*  its CReal image is the limit of the stationary tower.  The Gaussian *)
(*  / θ / functional equation are the residual layer 3 on top.         *)
(*                                                                    *)
(*  Over CReal (constructive Cauchy reals); the Q/Z reconstruction is   *)
(*  axiom-free, the CReal limit uses only the CReal completion.        *)
(* ================================================================= *)

From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals
        Reals.Cauchy.ConstructiveCauchyRealsMult
        Reals.Cauchy.ConstructiveCauchyAbs.
Require Import PrimeFactorizationN PrimeFactorizationExists PrimonGas
        ProductFormulaQ ArchimedeanTower CRealCv.
From Stdlib Require Import ZArith Znumtheory QArith Qabs Lqa Lia List.
Import ListNotations.
Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  A constant rational sequence converges to its CReal embedding.   *)
(* ----------------------------------------------------------------- *)

Lemma cvQ_const : forall q : Q, cvQ (fun _ => q) (inject_Q q).
Proof.
  intros q p; exists 0%nat; intros n _.
  rewrite <- (inject_Q_diff q q); apply inj_abs_le.
  assert (Hq : (q - q == 0)%Q) by ring.
  rewrite Hq; apply Qabs_Qle_condition; split; unfold Qle; simpl; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Eventually-stationary → CReal limit.                             *)
(* ----------------------------------------------------------------- *)

Theorem archimedean_climit : forall (a : nat -> Q) (n : Z) (K : nat), (0 < n)%Z ->
  (forall B, (K <= B)%nat -> (a B == inject_Z n)%Q) ->
  cvQ a (inject_Q (inject_Z n)).
Proof.
  intros a n K Hn Heq.
  apply (cvQ_eventually_eq a (fun _ => inject_Z n) (inject_Q (inject_Z n)) K).
  - intros m Hm; apply Heq; exact Hm.
  - apply cvQ_const.
Qed.

(* ----------------------------------------------------------------- *)
(*  The primorial reconstruction sequence converges to |n|_∞.        *)
(*  Any sequence a with a B = / fabs(primes_upto B) ks (a factorisa-  *)
(*  tion of n) for B ≥ ⌊n⌋ realises the reconstruction, hence → |n|_∞. *)
(* ----------------------------------------------------------------- *)

Theorem archimedean_recon_climit : forall (a : nat -> Q) (n : Z), (0 < n)%Z ->
  (forall B, (Z.to_nat n <= B)%nat ->
     exists ks, Forall prime (primes_upto B)
             /\ length (primes_upto B) = length ks
             /\ code (primes_upto B) ks = n
             /\ (a B == / fabs (primes_upto B) ks)%Q) ->
  cvQ a (inject_Q (inject_Z n)).
Proof.
  intros a n Hn Hrec.
  apply (archimedean_climit a n (Z.to_nat n) Hn).
  intros B HB; destruct (Hrec B HB) as [ks [Hpr [Hlen [Hcode Ha]]]].
  rewrite Ha, <- Hcode; symmetry; apply fabs_recip; [ exact Hpr | exact Hlen ].
Qed.

(* ----------------------------------------------------------------- *)
(*  The archimedean place at n, as the CReal limit of its stationary  *)
(*  primorial reconstruction.                                         *)
(* ----------------------------------------------------------------- *)

Corollary archimedean_place_climit : forall n : Z, (0 < n)%Z ->
  cvQ (fun _ => inject_Z n) (inject_Q (inject_Z n)).
Proof. intros n Hn; apply cvQ_const. Qed.

Print Assumptions archimedean_recon_climit.
Print Assumptions archimedean_place_climit.

(* ================================================================= *)
(*  END ArchimedeanCompletion.v                                      *)
(*  The stationary primorial tower (ArchimedeanTower) has a genuine    *)
(*  CReal limit: the reconstruction sequence converges to inject_Q     *)
(*  (inject_Z n), the CReal image of the archimedean value |n|_∞.      *)
(*  Layer 2 (completion) now attaches to layer 1 (the prime-defined    *)
(*  place); the residual Gaussian lives at layer 3 on top.            *)
(* ================================================================= *)
