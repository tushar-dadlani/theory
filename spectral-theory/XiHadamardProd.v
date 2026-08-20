(* ================================================================= *)
(*  XiHadamardProd.v  —  the Hadamard product over an arbitrary        *)
(*  ZeroEnum: PHASE 1, convergence.                                    *)
(*                                                                    *)
(*    hadamard_prod_cv : for rho enumerating the zeros of xi,          *)
(*      the partial products of  Efac z (rho n) = (1 - z/rho_n)e^{z/rho_n} *)
(*      converge, for every z.                                        *)
(*                                                                    *)
(*  WHY THIS IS SHORT.  The repo already carries a complete            *)
(*  Weierstrass-product apparatus, built for                           *)
(*      1/Gamma(z) = z e^{gamma z} prod (1 + z/k) e^{-z/k}.            *)
(*  Hadamard's factor is the SAME shape: with w := -z/rho,             *)
(*      (1 - z/rho) e^{z/rho} = (1 + w) e^{-w}.                        *)
(*  So nothing analytic had to be built -- only re-aimed:              *)
(*    * CWeierFactor.weier_dev_le   the factor estimate at a free w    *)
(*      (GammaCWeierstrass proves it only for w = z/k);                *)
(*    * CInfProd.Pprod_cv           sum |f n - 1| converges => the      *)
(*      partial products converge;                                     *)
(*    * XiZeroEnum.enum_sum_bound   sum 1/|rho_n|^2 <= 4 agrow,         *)
(*      UNIFORMLY in the number of terms -- which is exactly the        *)
(*      summability Pprod_cv wants.                                     *)
(*                                                                    *)
(*  Pprod_cv is choice-free (it is built from R_complete) and returns   *)
(*  a sig, so it can be used directly; no new axiom appears.           *)
(*                                                                    *)
(*  NOT IN THIS PHASE: the identity xi z = A e^{bz} . prod.  That needs *)
(*  relating prodfac (which is prod (z - rho)) to this product -- they  *)
(*  differ by prod(-rho) . e^{-z sum 1/rho_n}, and sum 1/rho_n need NOT *)
(*  converge, which is precisely why the e^{z/rho} factors are there -- *)
(*  and it needs LOCALLY UNIFORM convergence to feed the order-1 step,  *)
(*  whereas Pprod_cv gives only pointwise.  Axiom-clean.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CDeriv CexpFull CSeries CInfProd
        CWeierFactor CDyadicSum XiZeroEnum XiHgrow.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the Hadamard factor and its deviation bound                    *)
(* ----------------------------------------------------------------- *)
Definition Efac (z rho : C) : C :=
  Cmul (Cminus C1 (Cmul z (Cinv rho))) (Cexpf (Cmul z (Cinv rho))).

Definition KR (r : R) : R := r ^ 2 * (1 + 3 * (1 + r) * exp r).

Lemma KR_nonneg : forall r, 0 <= r -> 0 <= KR r.
Proof.
  intros r Hr. unfold KR. apply Rmult_le_pos; [ apply pow_le; lra | ].
  pose proof (exp_pos r). nra.
Qed.

Lemma Efac_dev_le : forall z rho, 1 <= Cmod rho ->
  Cmod (Cminus (Efac z rho) C1) <= KR (Cmod z) * / (Cmod rho) ^ 2.
Proof.
  intros z rho Hrho.
  assert (Hrne : rho <> C0).
  { intro Hc. rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hrho. lra. }
  set (w := Copp (Cmul z (Cinv rho))).
  (* the Hadamard factor IS the Weierstrass factor at w = -z/rho *)
  assert (Hopp : Copp w = Cmul z (Cinv rho)) by (unfold w; ring).
  assert (Hshape : Efac z rho = Cmul (Cadd C1 w) (Cexpf (Copp w))).
  { rewrite Hopp. unfold Efac, w. ring. }
  rewrite Hshape.
  (* |w| = |z| / |rho| *)
  assert (Hmw : Cmod w = Cmod z / Cmod rho).
  { unfold w. rewrite Cmod_opp, Cmod_mul, (Cmod_inv rho Hrne).
    unfold Rdiv. reflexivity. }
  assert (Hrpos : 0 < Cmod rho) by lra.
  assert (Hz0 : 0 <= Cmod z) by apply Cmod_nonneg.
  assert (HmwZ : Cmod w <= Cmod z).
  { rewrite Hmw. unfold Rdiv.
    assert (Hinv : / Cmod rho <= 1)
      by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
    nra. }
  assert (Hmwsq : Cmod w ^ 2 = Cmod z ^ 2 * / Cmod rho ^ 2).
  { rewrite Hmw. unfold Rdiv. rewrite Rpow_mult_distr, pow_inv. reflexivity. }
  eapply Rle_trans; [ apply weier_dev_le | ].
  (* replace Cmod w by Cmod z in the monotone factor, exactly as in the
     Gamma proof -- this is the step weier_dev_le deliberately left out *)
  assert (Hfac : (1 + Cmod w) * exp (Cmod w) <= (1 + Cmod z) * exp (Cmod z)).
  { apply Rmult_le_compat;
      [ pose proof (Cmod_nonneg w); lra | left; apply exp_pos | lra | ].
    apply exp_le; exact HmwZ. }
  assert (Hmono : 1 + 3 * (1 + Cmod w) * exp (Cmod w)
                  <= 1 + 3 * (1 + Cmod z) * exp (Cmod z)) by lra.
  rewrite Hmwsq. unfold KR.
  assert (Hpos : 0 <= Cmod z ^ 2 * / Cmod rho ^ 2)
    by (apply Rmult_le_pos; [ apply pow_le; lra
                            | left; apply Rinv_0_lt_compat; apply pow_lt; lra ]).
  apply Rle_trans with (Cmod z ^ 2 * / Cmod rho ^ 2
                        * (1 + 3 * (1 + Cmod z) * exp (Cmod z))).
  - apply Rmult_le_compat_l; [ exact Hpos | exact Hmono ].
  - apply Req_le. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  list sums vs sum_f_R0                                          *)
(* ----------------------------------------------------------------- *)
Lemma sumlist_app : forall (f : C -> R) (l1 l2 : list C),
  sumlist f (l1 ++ l2) = sumlist f l1 + sumlist f l2.
Proof.
  intros f l1 l2. induction l1 as [| x l1' IH]; cbn [app sumlist]; lra.
Qed.

Lemma sumlist_takeN : forall (rho : nat -> C) (N : nat),
  sumlist invsq (takeN rho (S N)) = sum_f_R0 (fun n => invsq (rho n)) N.
Proof.
  intros rho N. induction N as [| N IH].
  - cbn [takeN seq map sumlist sum_f_R0]. lra.
  - unfold takeN. rewrite seq_S, map_app, sumlist_app.
    unfold takeN in IH. rewrite IH, tech5.
    cbn [map sumlist]. replace (0 + S N)%nat with (S N) by lia. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  summability of the deviations along the enumeration            *)
(* ----------------------------------------------------------------- *)
Lemma sumR0_le : forall (A B : nat -> R) (N : nat),
  (forall i, A i <= B i) -> sum_f_R0 A N <= sum_f_R0 B N.
Proof.
  intros A B N H. induction N as [| N IH]; cbn [sum_f_R0]; [ apply H | ].
  pose proof (H (S N)). lra.
Qed.

Theorem Efac_devsum_cv : forall (rho : nat -> C),
  ZeroEnum rho -> (forall n, 1 <= Cmod (rho n)) ->
  forall z, { T | Un_cv (sum_f_R0 (dev (fun n => Efac z (rho n)))) T }.
Proof.
  intros rho Henum Hlow z.
  set (g := fun n => Efac z (rho n)).
  set (Un := sum_f_R0 (dev g)).
  assert (Hgrow : Un_growing Un).
  { intro N. unfold Un. rewrite tech5.
    pose proof (Cmod_nonneg (Cminus (g (S N)) C1)). unfold dev. lra. }
  assert (Hub : has_ub Un).
  { exists (KR (Cmod z) * (4 * agrow)). intros v [N ->]. unfold Un.
    apply Rle_trans with (sum_f_R0 (fun n => invsq (rho n) * KR (Cmod z)) N).
    - apply sumR0_le. intro i. unfold dev, g, invsq.
      rewrite Rmult_comm. apply Efac_dev_le. apply Hlow.
    - rewrite <- (scal_sum (fun n => invsq (rho n)) N (KR (Cmod z))).
      apply Rmult_le_compat_l;
        [ apply KR_nonneg; apply Cmod_nonneg | ].
      rewrite <- sumlist_takeN. apply enum_sum_bound; assumption. }
  destruct (growing_cv Un Hgrow Hub) as [l Hl]. exists l; exact Hl.
Defined.

(* ================================================================= *)
(*  D.  THE PRODUCT CONVERGES                                          *)
(* ================================================================= *)
Theorem hadamard_prod_cv : forall (rho : nat -> C),
  ZeroEnum rho -> (forall n, 1 <= Cmod (rho n)) ->
  forall z, { P : C | CUn_cv (Pprod (fun n => Efac z (rho n))) P }.
Proof.
  intros rho Henum Hlow z.
  destruct (Efac_devsum_cv rho Henum Hlow z) as [T HT].
  exact (Pprod_cv (fun n => Efac z (rho n)) T HT).
Defined.

Print Assumptions hadamard_prod_cv.
