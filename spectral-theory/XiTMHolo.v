(* ================================================================= *)
(*  XiTMHolo.v  —  the tail product T_M is ENTIRE.                     *)
(*                                                                    *)
(*    TM_holo : forall z, exists d, is_Cderiv (TM ...) z d.            *)
(*                                                                    *)
(*  This is the last analytic step of piece 2.  With it, the           *)
(*  construction                                                       *)
(*      H := Hcof M . (T_M)^{-1}                                       *)
(*  has everything it needs: xi = H . P is algebra, H is zero-free     *)
(*  from Hcof_ne0 plus tail_prod_ge, and H is holomorphic because      *)
(*  Hcof M is and T_M is (here) and T_M is nonvanishing.               *)
(*                                                                    *)
(*  It is now pure composition of things already proved:               *)
(*    tail_prod_unif      the tail converges uniformly on every disk;  *)
(*    unif_limit_ptcont   so the limit is continuous;                  *)
(*    unif_limit_holo     and, being a uniform limit of holomorphic    *)
(*                        functions, holomorphic.                      *)
(*  The one genuinely new ingredient is that each partial product is    *)
(*  itself entire IN z -- Efac_holo_z and Pprod_Efac_holo -- which is   *)
(*  routine (a linear factor times an exponential of a linear map).     *)
(*                                                                    *)
(*  Note the radius bookkeeping is free: unif_limit_holo concludes on   *)
(*  Cmod z < (Rr-1)/2, and Rr may be taken as large as one likes, so    *)
(*  choosing Rr := 2 |z| + 3 puts any given z strictly inside.          *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC CexpFull
        CexpfDeriv PerronRemovable CIntegral2 CSegInt CSeries CInfProd CMorera
        CDyadicSum XiZeroEnum XiHgrow XiHadamardProd XiHadamardUnif XiTailProd.
Open Scope R_scope.

Lemma is_Cderiv_val3 : forall F z d d', is_Cderiv F z d -> d = d' -> is_Cderiv F z d'.
Proof. intros F z d d' H E; subst; exact H. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  each factor, and each partial product, is entire in z          *)
(* ----------------------------------------------------------------- *)
Lemma Efac_holo_z : forall (r z : C), exists d, is_Cderiv (fun w => Efac w r) z d.
Proof.
  intros r z.
  assert (Hlin : is_Cderiv (fun w => Cmul w (Cinv r)) z (Cinv r)).
  { apply (is_Cderiv_val3 _ _ (Cadd (Cmul C1 (Cinv r)) (Cmul z C0)));
      [ apply (Cderiv_mul (fun w => w) (fun _ => Cinv r) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ]
      | ring ]. }
  assert (Hone : is_Cderiv (fun w => Cminus C1 (Cmul w (Cinv r))) z
                   (Cminus C0 (Cinv r)))
    by (apply (Cderiv_minus (fun _ => C1) (fun w => Cmul w (Cinv r)) z C0 (Cinv r));
        [ apply Cderiv_const | exact Hlin ]).
  assert (Hexp : is_Cderiv (fun w => Cexpf (Cmul w (Cinv r))) z
                   (Cmul (Cexpf (Cmul z (Cinv r))) (Cinv r)))
    by (apply (Cexpf_comp_deriv (fun w => Cmul w (Cinv r)) z (Cinv r) Hlin)).
  unfold Efac. eexists. apply Cderiv_mul; [ exact Hone | exact Hexp ].
Qed.

Lemma Pprod_Efac_holo : forall (rr : nat -> C) (n : nat) (z : C),
  exists d, is_Cderiv (fun w => Pprod (fun j => Efac w (rr j)) n) z d.
Proof.
  intros rr n. induction n as [| n IH]; intro z.
  - cbn [Pprod]. apply Efac_holo_z.
  - destruct (IH z) as [d1 Hd1]. destruct (Efac_holo_z (rr (S n)) z) as [d2 Hd2].
    change (fun w => Pprod (fun j => Efac w (rr j)) (S n))
      with (fun w => Cmul (Pprod (fun j => Efac w (rr j)) n) (Efac w (rr (S n)))).
    eexists. apply Cderiv_mul; [ exact Hd1 | exact Hd2 ].
Qed.

Lemma Pprod_Efac_ptcont : forall (rr : nat -> C) (n : nat),
  forall z eps, 0 < eps -> exists del, 0 < del /\
    forall z', Cmod (Cminus z' z) < del ->
      Cmod (Cminus (Pprod (fun j => Efac z' (rr j)) n)
                   (Pprod (fun j => Efac z (rr j)) n)) < eps.
Proof.
  intros rr n.
  exact (holo_ptcont (fun w => Pprod (fun j => Efac w (rr j)) n)
           (fun z => Pprod_Efac_holo rr n z)).
Qed.

Lemma Pprod_Efac_CcontC : forall (rr : nat -> C) (n : nat),
  CcontC (fun w => Pprod (fun j => Efac w (rr j)) n).
Proof.
  intros rr n. apply ptcont_CcontC. apply Pprod_Efac_ptcont.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the tail product as a function, and its regularity             *)
(* ----------------------------------------------------------------- *)
Section TMHolo.

Variable rho : nat -> C.
Hypothesis Henum : ZeroEnum rho.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).
Variable M : nat.

Definition TM (z : C) : C := proj1_sig (tail_prod_cv rho Henum Hlow M z).

Lemma TM_spec : forall z,
  CUn_cv (Pprod (fun j => Efac z (rsh rho M j))) (TM z).
Proof. intro z. exact (proj2_sig (tail_prod_cv rho Henum Hlow M z)). Qed.

(* uniform convergence on a neighbourhood of EVERY point *)
Lemma TM_unif_local : forall z0, exists r, 0 < r /\ forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat -> forall w, Cmod (Cminus w z0) < r ->
    Cmod (Cminus (Pprod (fun j => Efac w (rsh rho M j)) n) (TM w)) <= eps.
Proof.
  intro z0. exists 1. split; [ lra | ]. intros eps Heps.
  set (Rr := Cmod z0 + 1).
  assert (HRr : 0 < Rr) by (pose proof (Cmod_nonneg z0); unfold Rr; lra).
  destruct (tail_prod_unif rho Henum Hlow Rr HRr M TM TM_spec eps Heps)
    as [N HN].
  exists N. intros n Hn w Hw.
  assert (Hwm : Cmod w <= Rr).
  { assert (Htri : Cmod w <= Cmod (Cminus w z0) + Cmod z0)
      by (replace w with (Cadd (Cminus w z0) z0) at 1 by ring; apply Cmod_triangle).
    unfold Rr. lra. }
  left. exact (HN n Hn w Hwm).
Qed.

Lemma TM_ptcont : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall z', Cmod (Cminus z' z) < del -> Cmod (Cminus (TM z') (TM z)) < eps.
Proof.
  apply (unif_limit_ptcont
           (fun n w => Pprod (fun j => Efac w (rsh rho M j)) n) TM).
  - intros n z eps Heps. apply (Pprod_Efac_ptcont (rsh rho M) n z eps Heps).
  - exact TM_unif_local.
Qed.

Lemma TM_CcontC : CcontC TM.
Proof. apply ptcont_CcontC. exact TM_ptcont. Qed.

(* ================================================================= *)
(*  C.  T_M IS ENTIRE                                                  *)
(* ================================================================= *)
Theorem TM_holo : forall z, exists d, is_Cderiv TM z d.
Proof.
  intro z.
  pose proof (Cmod_nonneg z) as Hz0.
  set (Rr := 2 * Cmod z + 3).
  assert (HRr : 1 < Rr) by (unfold Rr; lra).
  apply (unif_limit_holo
           (fun n w => Pprod (fun j => Efac w (rsh rho M j)) n) TM Rr HRr).
  - intro n. apply Pprod_Efac_CcontC.
  - intros n w. apply Pprod_Efac_holo.
  - exact TM_CcontC.
  - exact TM_ptcont.
  - intros eps Heps.
    assert (HRpos : 0 < Rr) by (unfold Rr; lra).
    destruct (tail_prod_unif rho Henum Hlow Rr HRpos M TM TM_spec eps Heps)
      as [N HN].
    exists N. intros n Hn w Hw. left. apply HN; [ exact Hn | lra ].
  - unfold Rr. lra.
Qed.

End TMHolo.

Print Assumptions TM_holo.
