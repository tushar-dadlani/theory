(* ================================================================= *)
(*  XiHadamardGlue.v  —  the glue, part 3: ONE H on all of C.          *)
(*                                                                    *)
(*    xi_hadamard_global :                                             *)
(*      Hglob is entire, nowhere zero, and  xi z = Hglob z . P z       *)
(*      for EVERY z in C, P the Hadamard product over the zeros.       *)
(*                                                                    *)
(*  XiHadamardLocal produced, for each radius, SOME H on that disk.    *)
(*  Nothing there said two radii agree, and an existential per radius  *)
(*  cannot be assembled into a function.  Both gaps close here:        *)
(*                                                                    *)
(*   * XiHcofCoh.Hcof_TM_indep : the value Hcof M z . (TM M z)^{-1}    *)
(*     does not depend on M, over all M for which TM M z <> C0.  The   *)
(*     same block of Weierstrass factors divides xi's cofactor and     *)
(*     multiplies the tail product, so it cancels.                     *)
(*   * XiTMSelect.Msel : an admissible M as a FUNCTION of the radius.  *)
(*                                                                    *)
(*  So Hglob z is defined outright, taking the truncation Msel at the  *)
(*  radius Cmod z + 1 -- a formula, not a choice.  It varies with z,   *)
(*  which is exactly why M-independence is needed: near a point z0 all *)
(*  the truncations in play give one and the same value, so Hglob      *)
(*  agrees on a ball with a FIXED-M function, and                      *)
(*  is_Cderiv_ext_local hands over that function's derivative.         *)
(*                                                                    *)
(*  Zero-freeness needs a second appeal to independence: Msel is       *)
(*  chosen by the tail-sum test and knows nothing of Hcof_ne0's        *)
(*  threshold, so the value is recomputed at the max of the two.       *)
(*  Raising M is free -- Ttl is decreasing, so the tail test still     *)
(*  passes.                                                            *)
(*                                                                    *)
(*  WHAT REMAINS for the Hadamard factorization: SubQuadLog Hglob,     *)
(*  which feeds COrderOne.order_one_step_uncond and pins Hglob to      *)
(*  A . e^{bz}.  The factorization itself is now a statement about a   *)
(*  single entire zero-free function, which is what that theorem eats. *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CCutoff CHoloCalculus
        CSeries CInfProd JensenMultiZero CZeroListFactor
        RiemannXiEntire XiZeroEnum XiHadamardProd XiProdLimit
        XiHcof XiTailProd XiTMHolo XiHcofCoh XiTMSelect XiHadamardLocal.
Open Scope R_scope.

Section Glue.

Variable rho : nat -> C.
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Notation En := (HE rho Gseq HZ).

(* the truncation attached to a point, and the value it produces *)
Definition Mz (z : C) : nat := Msel rho En Hlow (Cmod z + 1).

Definition Hval (M : nat) (z : C) : C :=
  Cmul (Hcof rho Gseq M z) (Cinv (TM rho En Hlow M z)).

Definition Hglob (z : C) : C := Hval (Mz z) z.

Lemma TM_Mz_ne0 : forall z, TM rho En Hlow (Mz z) z <> C0.
Proof.
  intro z. unfold Mz.
  apply (TM_Msel_ne0 rho En Hlow (Cmod z + 1));
    [ pose proof (Cmod_nonneg z); lra | lra ].
Qed.

(* raising the truncation keeps the tail test, hence keeps TM nonzero *)
Lemma TM_up_ne0 : forall (r : R) (M : nat), 0 < r ->
  KR r * Ttl rho En Hlow M < u0 ->
  forall N, (M <= N)%nat -> forall z, Cmod z < r ->
  TM rho En Hlow N z <> C0.
Proof.
  intros r M Hr Hsm N HMN z Hz.
  apply (TM_ne0_disk rho En Hlow r Hr N); [ | exact Hz ].
  pose proof (Ttl_decr rho En Hlow M N HMN) as Hd.
  pose proof (KR_pos r Hr) as HK. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  near any point, Hglob IS a fixed-truncation function           *)
(* ----------------------------------------------------------------- *)
Lemma Hglob_fixed : forall z0 z, Cmod (Cminus z z0) < 1 ->
  Hglob z = Hval (Msel rho En Hlow (Cmod z0 + 2)) z.
Proof.
  intros z0 z Hz.
  assert (Hb : Cmod z < Cmod z0 + 2).
  { assert (Hzz : Cmod z <= Cmod (Cminus z z0) + Cmod z0).
    { replace z with (Cadd (Cminus z z0) z0) at 1 by ring. apply Cmod_triangle. }
    lra. }
  assert (Hr2 : 0 < Cmod z0 + 2) by (pose proof (Cmod_nonneg z0); lra).
  unfold Hglob, Hval.
  apply (Hcof_TM_indep rho En Hlow Gseq HZ);
    [ apply TM_Mz_ne0 | apply (TM_Msel_ne0 rho En Hlow _ Hr2 z Hb) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  entire                                                         *)
(* ----------------------------------------------------------------- *)
Theorem Hglob_holo : forall z0, exists d, is_Cderiv Hglob z0 d.
Proof.
  intro z0.
  set (M := Msel rho En Hlow (Cmod z0 + 2)).
  assert (Hr2 : 0 < Cmod z0 + 2) by (pose proof (Cmod_nonneg z0); lra).
  assert (Hne : TM rho En Hlow M z0 <> C0)
    by (apply (TM_Msel_ne0 rho En Hlow _ Hr2 z0); lra).
  destruct (Hcof_holo rho Gseq HZ M z0) as [d1 Hd1].
  destruct (TM_holo rho En Hlow M z0) as [d2 Hd2].
  eexists.
  apply (is_Cderiv_ext_local Hglob (Hval M) z0 _ 1 ltac:(lra));
    [ intros w Hw; apply Hglob_fixed; exact Hw | ].
  unfold Hval. apply Cderiv_div; [ exact Hd1 | exact Hd2 | exact Hne ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  nowhere zero                                                   *)
(* ----------------------------------------------------------------- *)
Theorem Hglob_ne0 : forall z, Hglob z <> C0.
Proof.
  intro z.
  set (r := Cmod z + 1).
  assert (Hr : 0 < r) by (unfold r; pose proof (Cmod_nonneg z); lra).
  destruct (Hcof_ne0 rho Gseq HZ r Hr) as [N0 HN0].
  set (N := Nat.max (Mz z) N0).
  assert (HMN : (Mz z <= N)%nat) by (unfold N; lia).
  assert (HN0N : (N0 <= N)%nat) by (unfold N; lia).
  assert (HTN : TM rho En Hlow N z <> C0).
  { apply (TM_up_ne0 r (Mz z) Hr); [ | exact HMN | unfold r; lra ].
    unfold Mz. apply (Msel_spec rho En Hlow r Hr). }
  assert (Heq : Hglob z = Hval N z)
    by (unfold Hglob, Hval;
        apply (Hcof_TM_indep rho En Hlow Gseq HZ); [ apply TM_Mz_ne0 | exact HTN ]).
  rewrite Heq. unfold Hval. apply Cmul_ne0.
  - apply (HN0 N HN0N z); unfold r; lra.
  - intro Hc.
    assert (Hone : Cmul (TM rho En Hlow N z) (Cinv (TM rho En Hlow N z)) = C1)
      by (field; exact HTN).
    rewrite Hc in Hone.
    assert (Hz0 : Cmul (TM rho En Hlow N z) C0 = C0) by ring.
    rewrite Hz0 in Hone. exact (C1_neq_C0 (eq_sym Hone)).
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the factorization                                              *)
(* ----------------------------------------------------------------- *)
Theorem Hglob_id : forall z,
  XiC z = Cmul (Hglob z) (Pinf rho Gseq HZ Hlow z).
Proof.
  intro z.
  pose proof (TM_Mz_ne0 z) as Hne.
  rewrite (Pinf_split rho Gseq HZ Hlow (Mz z) z),
          (Hcof_id rho Gseq HZ (Mz z) z).
  unfold Hglob, Hval. field. exact Hne.
Qed.

Theorem xi_hadamard_global :
  (forall z, exists d, is_Cderiv Hglob z d)
  /\ (forall z, Hglob z <> C0)
  /\ (forall z, XiC z = Cmul (Hglob z) (Pinf rho Gseq HZ Hlow z)).
Proof.
  split; [ exact Hglob_holo | split; [ exact Hglob_ne0 | exact Hglob_id ] ].
Qed.

End Glue.

Print Assumptions xi_hadamard_global.
