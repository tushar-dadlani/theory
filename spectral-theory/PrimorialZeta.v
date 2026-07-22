(* ================================================================= *)
(*  PrimorialZeta.v                                                   *)
(*                                                                    *)
(*  THE PRIMORIAL TOWER'S LIMIT IS zeta(2) -- the analytic half of the  *)
(*  Euler product formula, rigorously; the number-theoretic crux        *)
(*  (Euler's factorization) is cleanly ISOLATED as two hypotheses.      *)
(*                                                                    *)
(*  We already have:                                                   *)
(*    PrimorialEulerBound.EP_converges : the primorial tower EP n       *)
(*      converges (monotone + bounded), and                            *)
(*    ZetaConverge.zeta2_converges     : zpart -> zeta(2).              *)
(*                                                                    *)
(*  Proving lim EP n = zeta(2) is a squeeze that goes through the        *)
(*  identity  EP n = sum over {first n primes}-smooth m of 1/m^2.       *)
(*  That identity (unique factorization + reindexing) is the genuine     *)
(*  number-theoretic content; here we take exactly its two consequences  *)
(*  as HYPOTHESES and prove the rest in full:                          *)
(*                                                                    *)
(*    Hupper : forall n, EP P n <= Lz     (smooth subset of all N)      *)
(*    Hlower : forall N, exists n, zpart N <= EP P n                    *)
(*                              (every initial segment is eventually     *)
(*                               smooth, once n primes cover it)         *)
(*                                                                    *)
(*  Given these, tower_is_zeta : Un_cv (EP P) Lz -- the primorial-       *)
(*  relativized Euler product converges to zeta(2).  The two hypotheses  *)
(*  are precisely what EP n = sum_{smooth} 1/m^2 delivers; formalizing    *)
(*  that (unique factorization over the first n primes + reindexing +     *)
(*  small-numbers-are-smooth) is the deferred crux (LEDGER.md).         *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)

Require Import PrimorialEuler PrimorialEulerBound ZetaConverge.
From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* a convergent sequence bounded above by c has limit <= c *)
Lemma lim_le : forall (Un : nat -> R) l c,
  Un_cv Un l -> (forall n, Un n <= c) -> l <= c.
Proof.
  intros Un l c Hcv Hb.
  destruct (Rle_or_lt l c) as [Hle | Hlt]; [ exact Hle | exfalso ].
  set (eps := (l - c) / 2).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hcv eps Heps) as [N HN]; specialize (HN N (Nat.le_refl N)).
  unfold R_dist in HN; apply Rabs_def2 in HN; destruct HN as [_ Hlo].
  specialize (Hb N); unfold eps in *; lra.
Qed.

Section TowerZeta.

Variable P : nat -> R.
Hypothesis HP : forall i, INR i + 2 <= P i.

(* ----------------------------------------------------------------- *)
(*  THE REDUCTION: given the two crux bounds (Euler factorization),   *)
(*  the primorial tower converges to zeta(2).                        *)
(* ----------------------------------------------------------------- *)

Theorem tower_is_zeta :
  forall Lz : R,
    Un_cv zpart Lz ->                          (* Lz = zeta(2) *)
    (forall n, EP P n <= Lz) ->                (* CRUX 1: each rung <= zeta(2) *)
    (forall N, exists n, zpart N <= EP P n) -> (* CRUX 2: rungs eventually dominate *)
    Un_cv (EP P) Lz.
Proof.
  intros Lz HLz Hupper Hlower.
  destruct (EP_converges P HP) as [L HL].
  assert (Hgrow : Un_growing (EP P)) by (exact (EP_monotone P (HP2 P HP))).
  assert (Hle_lim : forall n, EP P n <= L) by (apply growing_ineq; assumption).
  assert (HLup : L <= Lz) by (apply (lim_le (EP P) L Lz HL Hupper)).
  assert (Hz_le : forall N, zpart N <= L).
  { intro N; destruct (Hlower N) as [n Hn].
    apply Rle_trans with (EP P n); [ exact Hn | apply Hle_lim ]. }
  assert (HLlo : Lz <= L) by (apply (lim_le zpart Lz L HLz Hz_le)).
  assert (HeqL : L = Lz) by (apply Rle_antisym; assumption).
  rewrite <- HeqL; exact HL.
Qed.

(* instantiated at the genuine zeta(2) limit from ZetaConverge *)
Corollary tower_is_zeta2 :
  (forall n, EP P n <= proj1_sig zeta2_converges) ->
  (forall N, exists n, zpart N <= EP P n) ->
  Un_cv (EP P) (proj1_sig zeta2_converges).
Proof.
  exact (tower_is_zeta (proj1_sig zeta2_converges) (proj2_sig zeta2_converges)).
Qed.

End TowerZeta.

Print Assumptions tower_is_zeta.

(* ================================================================= *)
(*  END PrimorialZeta.v                                               *)
(*  The primorial tower converges to zeta(2) (Euler product formula),  *)
(*  proved rigorously modulo the two isolated crux hypotheses (each     *)
(*  rung <= zeta(2), and rungs eventually dominate every initial         *)
(*  segment) -- exactly the content of EP n = sum_{smooth} 1/m^2.       *)
(*  Uses the classical Reals axioms (quarantined).                    *)
(* ================================================================= *)
