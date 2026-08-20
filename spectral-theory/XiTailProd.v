(* ================================================================= *)
(*  XiTailProd.v  —  the TAIL products: uniformly convergent,          *)
(*  uniformly near 1, and uniformly bounded away from 0.               *)
(*                                                                    *)
(*    tail_prod_unif  : the tail partial products converge uniformly   *)
(*                      on every closed disk;                          *)
(*    tail_prod_near1 : and stay within exp(KR Rr . dtail M) - 1 of 1;  *)
(*    tail_prod_ge    : so for M large they never drop below 1/2.      *)
(*                                                                    *)
(*  WHY THE TAIL AND NOT THE WHOLE PRODUCT.  Piece 2 wants an entire,  *)
(*  zero-free H with xi = H . P.  Taking H as a limit of the cofactors  *)
(*  Hcof N fails: making that converge uniformly ACROSS the zeros       *)
(*  needs |Hcof M| bounded on a closed disk, i.e. compactness, which    *)
(*  this development avoids throughout.  The way round is to not take   *)
(*  that limit at all.  Since xi = Hcof M . Pprod M and                 *)
(*  P = Pprod M . T_M, one can DEFINE                                   *)
(*                                                                    *)
(*      H := Hcof M . (T_M)^{-1},                                       *)
(*                                                                    *)
(*  for M so large that every remaining rho_k lies outside the disk.    *)
(*  Then xi = H . P is algebra, H is zero-free because Hcof M is        *)
(*  (Hcof_ne0) and T_M is not, and the only analysis left concerns      *)
(*  T_M -- a tail product that is uniformly NEAR 1 and BOUNDED BELOW,   *)
(*  hence far better behaved than Hcof.  No boundedness on a compact    *)
(*  anywhere.  This file supplies the T_M facts.                        *)
(*                                                                    *)
(*  HOW IT IS ALMOST FREE.  The phase-2 section only ever used the      *)
(*  enumeration through a CAP ON THE INVERSE-SQUARE SUMS, so that       *)
(*  hypothesis is now abstract (Sb).  A shifted tail rho' n :=          *)
(*  rho (S (M + n)) satisfies the same cap with Sb the TAIL of the sum, *)
(*  which tends to 0.  So the tail statements are the phase-2           *)
(*  statements INSTANTIATED, not re-proved -- and the shrinking Sb is   *)
(*  exactly what makes the tail cluster around 1.  Axiom-clean.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CDeriv CSeries CInfProd CInfProdUnif
        CDyadicSum XiZeroEnum XiHgrow XiHadamardProd XiHadamardUnif.
Open Scope R_scope.

Section TailProd.

Variable rho : nat -> C.
Hypothesis Henum : ZeroEnum rho.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

(* the shifted enumeration and the tail of the inverse-square sum *)
Definition rsh (M : nat) : nat -> C := fun n => rho (S (M + n)).

Lemma rsh_low : forall M n, 1 <= Cmod (rsh M n).
Proof. intros M n. unfold rsh. apply Hlow. Qed.

Lemma invsq_nonneg : forall n, 0 <= invsq (rho n).
Proof.
  intro n. unfold invsq. left. apply Rinv_0_lt_compat. apply pow_lt.
  pose proof (Hlow n). lra.
Qed.

(* the total inverse-square sum, and its tail *)
Definition Tsum_cv : { T | Un_cv (sum_f_R0 (fun n => invsq (rho n))) T }.
Proof.
  set (Un := sum_f_R0 (fun n => invsq (rho n))).
  assert (Hgrow : Un_growing Un).
  { intro N. unfold Un. rewrite tech5. pose proof (invsq_nonneg (S N)). lra. }
  assert (Hub : has_ub Un).
  { exists (4 * agrow). intros v [N ->]. unfold Un.
    apply (enum_invsq_bound rho Henum Hlow). }
  destruct (growing_cv Un Hgrow Hub) as [l Hl]. exists l; exact Hl.
Defined.

Definition Tsum : R := proj1_sig Tsum_cv.

Lemma Tsum_spec : Un_cv (sum_f_R0 (fun n => invsq (rho n))) Tsum.
Proof. exact (proj2_sig Tsum_cv). Qed.

Definition Ttl (M : nat) : R := Tsum - sum_f_R0 (fun n => invsq (rho n)) M.

Lemma Ttl_nonneg : forall M, 0 <= Ttl M.
Proof.
  intro M. unfold Ttl.
  assert (Hle : sum_f_R0 (fun n => invsq (rho n)) M <= Tsum).
  { apply (growing_ineq (sum_f_R0 (fun n => invsq (rho n))));
      [ | apply Tsum_spec ].
    intro n. rewrite tech5. pose proof (invsq_nonneg (S n)). lra. }
  lra.
Qed.

(* the shifted enumeration is capped by the TAIL -- the whole point *)
Lemma rsh_sum : forall M N, sum_f_R0 (fun n => invsq (rsh M n)) N <= Ttl M.
Proof.
  intros M N. unfold rsh, Ttl.
  apply (shift_invsq_tail rho Tsum M invsq_nonneg Tsum_spec).
Qed.

(* the tail product converges pointwise -- same generalisation *)
Definition tail_prod_cv (M : nat) (z : C)
  : { P : C | CUn_cv (Pprod (fun j => Efac z (rsh M j))) P } :=
  hadamard_prod_cv_gen (rsh M) (Ttl M) (rsh_low M) (rsh_sum M) z.

(* ----------------------------------------------------------------- *)
(*  A.  the tail products stay near 1, uniformly on the disk           *)
(* ----------------------------------------------------------------- *)
Theorem tail_prod_near1 : forall (Rr : R), 0 < Rr ->
  forall M z, Cmod z <= Rr -> forall k,
  Cmod (Cminus (Pprod (fun j => Efac z (rsh M j)) k) C1)
  <= exp (KR Rr * Ttl M) - 1.
Proof.
  intros Rr HR M z Hz k.
  exact (Pprod_near1 (rsh M) (rsh_low M) (Ttl M) (rsh_sum M) Rr HR z Hz k).
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  hence bounded away from 0 once the tail is small               *)
(* ----------------------------------------------------------------- *)
Theorem tail_prod_ge : forall (Rr : R), 0 < Rr ->
  forall M, exp (KR Rr * Ttl M) - 1 <= / 2 ->
  forall z, Cmod z <= Rr -> forall k,
  / 2 <= Cmod (Pprod (fun j => Efac z (rsh M j)) k).
Proof.
  intros Rr HR M Hsmall z Hz k.
  set (q := Cmod (Pprod (fun j => Efac z (rsh M j)) k)).
  pose proof (tail_prod_near1 Rr HR M z Hz k) as Hb.
  pose proof (Cmod_diff_le (Pprod (fun j => Efac z (rsh M j)) k) C1) as Hd.
  rewrite Cmod_C1 in Hd. fold q in Hd.
  assert (Habs : Rabs (q - 1) <= / 2) by lra.
  assert (Hneg : - Rabs (q - 1) <= q - 1).
  { pose proof (Rle_abs (- (q - 1))) as H. rewrite Rabs_Ropp in H. lra. }
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  and converge uniformly on the disk                             *)
(* ----------------------------------------------------------------- *)
Theorem tail_prod_unif : forall (Rr : R), 0 < Rr -> forall M,
  forall (P : C -> C),
    (forall z, CUn_cv (Pprod (fun j => Efac z (rsh M j))) (P z)) ->
    forall eps, 0 < eps ->
      exists N, forall n, (N <= n)%nat ->
        forall z, Cmod z <= Rr ->
          Cmod (Cminus (Pprod (fun j => Efac z (rsh M j)) n) (P z)) < eps.
Proof.
  intros Rr HR M P HP eps Heps.
  exact (hadamard_prod_unif (rsh M) (rsh_low M) (Ttl M) (rsh_sum M) Rr HR
           P HP eps Heps).
Qed.

End TailProd.

Print Assumptions tail_prod_near1.
Print Assumptions tail_prod_unif.
