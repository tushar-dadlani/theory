(* ================================================================= *)
(*  MobiusReciprocal.v                                                *)
(*                                                                    *)
(*  The MOBIUS / INVERSION side of the primon-gas bridge, over Q,      *)
(*  axiom-free -- the reciprocal of the Euler factor.                  *)
(*                                                                    *)
(*  PrimonGas.v built the zeta side: the single-mode partition         *)
(*  function psum x K = sum_{k<K} x^k (-> 1/(1-x)).  Its RECIPROCAL     *)
(*  is (1 - x), and that is exactly the per-mode Mobius Dirichlet       *)
(*  series                                                            *)
(*                                                                    *)
(*     sum_k mu(p^k) x^k  =  1 - x    (mu(1)=1, mu(p)=-1, mu(p^{>=2})=0)*)
(*                                                                    *)
(*  a FINITE series (only two nonzero terms).  So:                     *)
(*    - mumode x = 1 - x is the per-mode Mobius series (mumode_is_-     *)
(*      museries);                                                     *)
(*    - mumode x * psum x K = 1 - x^K  is the per-mode Dirichlet        *)
(*      convolution zeta * mu  (mu_zeta_id, = PrimonGas.geom_closed);   *)
(*      as K -> infinity the RHS -> 1 = delta, i.e. Mobius inversion.   *)
(*    - over a finite prime set, prod_p mumode(x_p) times the Euler     *)
(*      product = prod_p (1 - x_p^K)  (mu_zeta_product): the reciprocal *)
(*      Euler product  prod(1 - p^{-s}) = 1/zeta  (= sum_n mu(n) n^-s). *)
(* ================================================================= *)

Require Import PrimonGas.
From Stdlib Require Import QArith Lqa ZArith List Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  1.  THE MOBIUS FUNCTION ON PRIME POWERS AND THE mu-SERIES         *)
(* ================================================================= *)

(* Mobius of p^k (independent of p):  1, -1, 0, 0, 0, ... *)
Definition mu_pp (k : nat) : Z :=
  match k with O => 1 | S O => -1 | S (S _) => 0 end.

(* the per-mode Mobius series, in closed form *)
Definition mumode (x : Q) : Q := 1 - x.

(* the k-th term and the truncated Mobius Dirichlet series *)
Definition muterm (x : Q) (k : nat) : Q := inject_Z (mu_pp k) * qpow x k.
Definition museries (x : Q) (K : nat) : Q := qsum (map (muterm x) (seq 0 K)).

Lemma museries_rec : forall x K, museries x (S K) == museries x K + muterm x K.
Proof.
  intros x K; unfold museries, muterm.
  rewrite seq_S, map_app, qsum_app; simpl; ring.
Qed.

(* from K >= 2 on, the series has collapsed to its two nonzero terms *)
Lemma museries_from2 : forall x n, museries x (S (S n)) == 1 - x.
Proof.
  intros x n; induction n as [|n IH].
  - unfold museries, muterm; simpl; ring.
  - rewrite museries_rec, IH; unfold muterm.
    change (mu_pp (S (S n))) with 0%Z.
    replace (inject_Z 0) with 0 by reflexivity; ring.
Qed.

(* mumode = 1 - x really is the Mobius series sum_k mu(p^k) x^k *)
Theorem mumode_is_museries : forall x K, (2 <= K)%nat -> museries x K == mumode x.
Proof.
  intros x K HK; unfold mumode.
  destruct K as [|[|n]]; [ exfalso; lia | exfalso; lia | apply museries_from2 ].
Qed.

(* ================================================================= *)
(*  2.  THE PER-MODE DIRICHLET CONVOLUTION  zeta * mu = delta         *)
(* ================================================================= *)

(* mumode * psum = 1 - x^K  (= PrimonGas.geom_closed): the truncated    *)
(* Dirichlet convolution of the Mobius series and the zeta series; the  *)
(* RHS -> 1 (= delta) as K -> infinity, i.e. Mobius inversion.          *)
Theorem mu_zeta_id : forall x K, mumode x * psum x K == 1 - qpow x K.
Proof. intros x K; unfold mumode; apply geom_closed. Qed.

(* ================================================================= *)
(*  3.  THE MULTI-PRIME RECIPROCAL EULER PRODUCT  prod(1-p^-s) = 1/zeta *)
(* ================================================================= *)

Lemma qprod_map_ext : forall (A : Type) (f g : A -> Q) (l : list A),
  (forall a, f a == g a) -> qprod (map f l) == qprod (map g l).
Proof.
  intros A f g l H; induction l as [|a l IH]; simpl;
    [ reflexivity | rewrite (H a), IH; reflexivity ].
Qed.

Lemma qprod_mult : forall (A : Type) (f g : A -> Q) (l : list A),
  qprod (map f l) * qprod (map g l) == qprod (map (fun a => f a * g a) l).
Proof.
  intros A f g l; induction l as [|a l IH]; simpl;
    [ ring | rewrite <- IH; ring ].
Qed.

(* the Mobius product times the Euler product is prod_p (1 - x_p^K),     *)
(* which -> 1 as K -> infinity: prod_p (1 - p^{-s}) is the RECIPROCAL of  *)
(* the Euler product, i.e. 1/zeta(s) = sum_n mu(n) n^{-s}.               *)
Theorem mu_zeta_product : forall xs K,
  qprod (map mumode xs) * qprod (map (fun x => psum x K) xs)
  == qprod (map (fun x => 1 - qpow x K) xs).
Proof.
  intros xs K; rewrite qprod_mult.
  apply qprod_map_ext; intro x; apply mu_zeta_id.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM — axiom-free over Q                               *)
(* ----------------------------------------------------------------- *)

Theorem mobius_reciprocal :
  (* mumode is the per-mode Mobius series sum_k mu(p^k) x^k *)
  (forall x K, (2 <= K)%nat -> museries x K == mumode x)
  (* per-mode Dirichlet convolution zeta * mu = 1 - x^K (-> delta) *)
  /\ (forall x K, mumode x * psum x K == 1 - qpow x K)
  (* multi-prime reciprocal Euler product: prod(mu) * prod(zeta) = prod(1-x^K) *)
  /\ (forall xs K, qprod (map mumode xs) * qprod (map (fun x => psum x K) xs)
                   == qprod (map (fun x => 1 - qpow x K) xs)).
Proof.
  split; [ exact mumode_is_museries | ].
  split; [ exact mu_zeta_id | exact mu_zeta_product ].
Qed.

Print Assumptions mobius_reciprocal.

(* ================================================================= *)
(*  END MobiusReciprocal.v                                            *)
(*  The Mobius reciprocal of the Euler factor: (1-x) = sum mu(p^k)x^k,  *)
(*  zeta * mu = delta per mode, and prod(1-p^-s) = 1/zeta.              *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
