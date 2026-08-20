(* ================================================================= *)
(*  XiProdFactor.v  —  where the DIVERGENT LINEAR TERM goes.           *)
(*                                                                    *)
(*    xi_prod_factor : for rho enumerating the zeros of xi and any N,  *)
(*      there is an ENTIRE, pointwise-continuous H with                *)
(*                                                                    *)
(*        xi z = H z . Pprod (fun k => Efac z (rho k)) N   for all z.  *)
(*                                                                    *)
(*  THE PROBLEM.  ZeroEnum gives xi = prodfac (takeN rho (S N)) . G,   *)
(*  where prodfac is prod (z - rho).  The Hadamard product uses         *)
(*  Efac z rho = (1 - z/rho) e^{z/rho} instead, and                     *)
(*                                                                    *)
(*     prod (z - rho_n)  =  [prod (-rho_n)] . [prod (1 - z/rho_n)]      *)
(*                       =  C_N . e^{-z . S_N} . prod Efac,             *)
(*     C_N := prod (-rho_n),   S_N := sum 1/rho_n.                      *)
(*                                                                    *)
(*  NEITHER C_N NOR S_N CONVERGES.  Only sum 1/|rho_n|^2 does -- which  *)
(*  is exactly why Weierstrass put the e^{z/rho} factors there in the   *)
(*  first place.  So one cannot pass to the limit factor by factor.     *)
(*                                                                    *)
(*  THE RESOLUTION.  Do not try to.  Absorb both divergent pieces into  *)
(*  the cofactor:                                                      *)
(*                                                                    *)
(*     H_N z := C_N . e^{-z S_N} . G_N z,                              *)
(*                                                                    *)
(*  which is still entire (a constant, an exponential of a linear map,  *)
(*  and an entire G).  Then xi = H_N . Pprod_N EXACTLY, for every N.    *)
(*  Since Pprod_N converges (phase 1) and xi is fixed, H_N is forced to *)
(*  converge too -- and its limit is where the b of e^{a+bz} comes from. *)
(*  The divergence never has to be confronted head-on.                  *)
(*                                                                    *)
(*  Everything here is an identity, not an estimate: two list           *)
(*  inductions (prodfac_Wlist, Wlist_takeN) and the exponential law     *)
(*  e^{u} e^{-u} = 1.  Axiom-clean.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC
        CexpFull CexpfDeriv CSine CInfProd
        JensenMultiZero CZeroListFactor RiemannXiEntire
        XiZeroEnum XiHadamardProd.
Open Scope R_scope.

Lemma is_Cderiv_val2 : forall F z d d', is_Cderiv F z d -> d = d' -> is_Cderiv F z d'.
Proof. intros F z d d' H E; subst; exact H. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the Weierstrass list product, and the reciprocal sum           *)
(* ----------------------------------------------------------------- *)
Fixpoint Wlist (l : list C) (z : C) : C :=
  match l with
  | nil => C1
  | r :: t => Cmul (Efac z r) (Wlist t z)
  end.

Fixpoint Slist (l : list C) : C :=
  match l with
  | nil => C0
  | r :: t => Cadd (Cinv r) (Slist t)
  end.

(* ----------------------------------------------------------------- *)
(*  B.  THE ABSORPTION IDENTITY                                        *)
(*                                                                    *)
(*    prod (z - rho)  =  [prod (-rho)] . [prod Efac] . e^{-z sum 1/rho} *)
(*                                                                    *)
(*  Note prod (-rho) is just prodfac l C0, so no new constant is needed.*)
(* ----------------------------------------------------------------- *)
Lemma prodfac_Wlist : forall (l : list C) (z : C),
  (forall r, In r l -> r <> C0) ->
  prodfac l z
  = Cmul (Cmul (prodfac l C0) (Wlist l z)) (Cexpf (Copp (Cmul z (Slist l)))).
Proof.
  induction l as [| r t IH]; intros z Hne.
  - cbn [prodfac Wlist Slist].
    replace (Copp (Cmul z C0)) with C0 by ring. rewrite Cexpf_C0. ring.
  - assert (Hr : r <> C0) by (apply Hne; left; reflexivity).
    assert (Ht : forall x, In x t -> x <> C0)
      by (intros x Hx; apply Hne; right; exact Hx).
    cbn [prodfac Wlist Slist].
    rewrite (IH z Ht). unfold Efac.
    replace (Copp (Cmul z (Cadd (Cinv r) (Slist t))))
      with (Cadd (Copp (Cmul z (Cinv r))) (Copp (Cmul z (Slist t)))) by ring.
    rewrite Cexpf_add.
    (* the two exponentials of opposite argument cancel *)
    assert (Hee : Cmul (Cexpf (Cmul z (Cinv r))) (Cexpf (Copp (Cmul z (Cinv r)))) = C1).
    { rewrite <- Cexpf_add.
      replace (Cadd (Cmul z (Cinv r)) (Copp (Cmul z (Cinv r)))) with C0 by ring.
      apply Cexpf_C0. }
    transitivity
      (Cmul (Cmul (Cmul (Cminus C0 r) (Cminus C1 (Cmul z (Cinv r))))
                  (Cmul (Cexpf (Cmul z (Cinv r))) (Cexpf (Copp (Cmul z (Cinv r))))))
            (Cmul (Cmul (prodfac t C0) (Wlist t z))
                  (Cexpf (Copp (Cmul z (Slist t)))))).
    + rewrite Hee.
      assert (Hzr : Cmul (Cminus C0 r) (Cminus C1 (Cmul z (Cinv r))) = Cminus z r)
        by (field; exact Hr).
      rewrite Hzr. ring.
    + ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the list product IS the partial product of phase 1             *)
(* ----------------------------------------------------------------- *)
Lemma Wlist_app : forall l1 l2 z,
  Wlist (l1 ++ l2) z = Cmul (Wlist l1 z) (Wlist l2 z).
Proof.
  induction l1 as [| x l1' IH]; intros l2 z; cbn [app Wlist];
    [ ring | rewrite IH; ring ].
Qed.

Lemma Wlist_takeN : forall (rho : nat -> C) (z : C) (N : nat),
  Wlist (takeN rho (S N)) z = Pprod (fun k => Efac z (rho k)) N.
Proof.
  intros rho z N. induction N as [| N IH].
  - cbn [takeN seq map Wlist Pprod]. ring.
  - unfold takeN. rewrite seq_S, map_app, Wlist_app.
    unfold takeN in IH. rewrite IH.
    cbn [map Wlist]. replace (0 + S N)%nat with (S N) by lia.
    cbn [Pprod]. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  e^{-z S} is entire                                             *)
(* ----------------------------------------------------------------- *)
Lemma Cexpf_lin_holo : forall (S z : C),
  exists d, is_Cderiv (fun w => Cexpf (Copp (Cmul w S))) z d.
Proof.
  intros S z.
  assert (Hlin : is_Cderiv (fun w => Cmul w S) z S).
  { apply (is_Cderiv_val2 _ _ (Cadd (Cmul C1 S) (Cmul z C0)));
      [ apply (Cderiv_mul (fun w => w) (fun _ => S) z C1 C0);
        [ apply Cderiv_id | apply Cderiv_const ]
      | ring ]. }
  assert (Hd : is_Cderiv (fun w => Copp (Cmul w S)) z (Copp S))
    by (apply Cderiv_opp; exact Hlin).
  eexists. apply (Cexpf_comp_deriv (fun w => Copp (Cmul w S)) z (Copp S) Hd).
Qed.

(* ================================================================= *)
(*  E.  THE FACTORISATION                                              *)
(* ================================================================= *)
Theorem xi_prod_factor : forall (rho : nat -> C), ZeroEnum rho -> forall N : nat,
  exists H : C -> C,
    (forall z, XiC z = Cmul (H z) (Pprod (fun k => Efac z (rho k)) N)) /\
    ptcont H /\ (forall R2, disk_holo H R2).
Proof.
  intros rho Henum N.
  destruct Henum as [Hne [Hesc [Hpre Hcomp]]].
  destruct (Hpre (S N)) as [G [Hid [Hptc Hhol]]].
  assert (Hlne : forall r, In r (takeN rho (S N)) -> r <> C0).
  { intros r Hr. unfold takeN in Hr. apply in_map_iff in Hr.
    destruct Hr as [n [Hn _]]. rewrite <- Hn. apply Hne. }
  (* H absorbs the divergent constant AND the divergent exponential *)
  set (H := fun z => Cmul (Cmul (prodfac (takeN rho (S N)) C0)
                               (Cexpf (Copp (Cmul z (Slist (takeN rho (S N)))))))
                          (G z)).
  assert (Hhol' : forall z, exists d, is_Cderiv H z d).
  { intro z.
    destruct (Cexpf_lin_holo (Slist (takeN rho (S N))) z) as [d1 Hd1].
    destruct (Hhol (Cmod z + 1) z ltac:(lra)) as [d2 Hd2].
    unfold H. eexists. apply Cderiv_mul; [ | exact Hd2 ].
    apply (Cderiv_mul (fun _ => prodfac (takeN rho (S N)) C0)
             (fun w => Cexpf (Copp (Cmul w (Slist (takeN rho (S N)))))) z C0 d1);
      [ apply Cderiv_const | exact Hd1 ]. }
  exists H. split; [ | split ].
  - intro z.
    rewrite (Hid z), (prodfac_Wlist (takeN rho (S N)) z Hlne),
            (Wlist_takeN rho z N).
    unfold H. ring.
  - exact (holo_ptcont H Hhol').
  - intros R2 z _. apply Hhol'.
Qed.

Print Assumptions xi_prod_factor.
