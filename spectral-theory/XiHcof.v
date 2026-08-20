(* ================================================================= *)
(*  XiHcof.v  —  piece 2a: the ENTIRE cofactor sequence.               *)
(*                                                                    *)
(*  THE SUBTLETY.  Cinv C0 = C0 in this development, so the naive       *)
(*  quotient Hseq N z = xi z . (Pprod N z)^{-1} VANISHES at each zero   *)
(*  rho_k rather than extending across it.  It is therefore NOT the     *)
(*  analytic cofactor, and its limit is not the H that                  *)
(*  order_one_step_uncond wants.  The analytic cofactor is the one      *)
(*  XiProdFactor built,                                                *)
(*                                                                    *)
(*      Hcof N z = C_N . e^{-z S_N} . G_N z,                           *)
(*                                                                    *)
(*  which is entire and agrees with Hseq only off the zero set.        *)
(*                                                                    *)
(*  BUT G_N sits behind a per-N existential in ZeroEnum, and turning    *)
(*  that family into a function nat -> C -> C is exactly the `choice`   *)
(*  we deferred.  Since ZeroEnum is a HYPOTHESIS, the fix is free:      *)
(*  ZeroEnumG packages the cofactors as a given family Gseq.  Any       *)
(*  genuine enumeration comes with one (G_N is determined off the       *)
(*  zeros and extends entirely), so this asks for nothing false --      *)
(*  it just declines to conjure a function out of an existential.       *)
(*  ZeroEnumG_ZeroEnum shows the packaged form is stronger.             *)
(*                                                                    *)
(*  Clause 4 is stated in the EVENTUALLY-zero-free form (all N beyond    *)
(*  some N0), which is what is true and what makes Hcof_ne0 immediate;  *)
(*  once a prefix has caught every zero in a disk, so has every longer  *)
(*  prefix.                                                            *)
(*                                                                    *)
(*  NOT IN THIS FILE: convergence of Hcof ACROSS the zeros, and hence   *)
(*  entirety and zero-freeness of the limit.  Off the zero set          *)
(*  Hcof_cv_off settles it; at a zero the two sides genuinely differ    *)
(*  and a Cauchy-formula argument on a surrounding circle is needed.    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC CexpFull
        CSeries CInfProd JensenMultiZero CZeroListFactor RiemannXiEntire
        XiZeroEnum XiHadamardProd XiProdFactor XiProdLimit.
Open Scope R_scope.

Lemma CUn_cv_ext : forall (u v : nat -> C) (l : C),
  (forall n, u n = v n) -> CUn_cv u l -> CUn_cv v l.
Proof.
  intros u v l Heq Hcv eps Heps.
  destruct (Hcv eps Heps) as [N HN]. exists N. intros n Hn.
  rewrite <- (Heq n). apply HN; exact Hn.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  the enumeration, with its cofactors packaged                   *)
(* ----------------------------------------------------------------- *)
Definition ZeroEnumG (rho : nat -> C) (Gseq : nat -> C -> C) : Prop :=
  (forall n, rho n <> C0)
  /\ (forall B, exists N, forall n, (N <= n)%nat -> B <= Cmod (rho n))
  /\ (forall N, (forall z, XiC z = Cmul (prodfac (takeN rho N) z) (Gseq N z))
              /\ ptcont (Gseq N) /\ (forall R2, disk_holo (Gseq N) R2))
  /\ (forall R, 0 < R -> exists N0, forall N, (N0 <= N)%nat ->
        forall z, Cmod z < R -> Gseq N z <> C0).

Lemma ZeroEnumG_ZeroEnum : forall rho Gseq, ZeroEnumG rho Gseq -> ZeroEnum rho.
Proof.
  intros rho Gseq [Hne [Hesc [Hpre Hfree]]].
  split; [ exact Hne | ]. split; [ exact Hesc | ]. split.
  - intro N. destruct (Hpre N) as [Hid [Hptc Hhol]].
    exists (Gseq N). split; [ exact Hid | split; [ exact Hptc | exact Hhol ] ].
  - intros R HR. destruct (Hfree R HR) as [N0 HN0].
    destruct (Hpre N0) as [Hid [Hptc Hhol]].
    exists N0, (Gseq N0). split; [ exact Hid | ].
    split; [ exact Hptc | ]. split; [ exact Hhol | ].
    intros z Hz. apply HN0; [ lia | exact Hz ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the ENTIRE cofactor                                            *)
(* ----------------------------------------------------------------- *)
Definition Hcof (rho : nat -> C) (Gseq : nat -> C -> C) (N : nat) (z : C) : C :=
  Cmul (Cmul (prodfac (takeN rho (S N)) C0)
             (Cexpf (Copp (Cmul z (Slist (takeN rho (S N)))))))
       (Gseq (S N) z).

Lemma Hcof_id : forall rho Gseq, ZeroEnumG rho Gseq -> forall N z,
  XiC z = Cmul (Hcof rho Gseq N z) (Pprod (fun k => Efac z (rho k)) N).
Proof.
  intros rho Gseq HZ N z.
  destruct HZ as [Hne [_ [Hpre _]]].
  destruct (Hpre (S N)) as [Hid _].
  assert (Hlne : forall r, In r (takeN rho (S N)) -> r <> C0).
  { intros r Hr. unfold takeN in Hr. apply in_map_iff in Hr.
    destruct Hr as [n [Hn _]]. rewrite <- Hn. apply Hne. }
  rewrite (Hid z), (prodfac_Wlist (takeN rho (S N)) z Hlne),
          (Wlist_takeN rho z N).
  unfold Hcof. ring.
Qed.

Lemma Hcof_holo : forall rho Gseq, ZeroEnumG rho Gseq -> forall N z,
  exists d, is_Cderiv (Hcof rho Gseq N) z d.
Proof.
  intros rho Gseq HZ N z.
  destruct HZ as [_ [_ [Hpre _]]].
  destruct (Hpre (S N)) as [_ [_ Hhol]].
  destruct (Cexpf_lin_holo (Slist (takeN rho (S N))) z) as [d1 Hd1].
  destruct (Hhol (Cmod z + 1) z ltac:(lra)) as [d2 Hd2].
  unfold Hcof. eexists. apply Cderiv_mul; [ | exact Hd2 ].
  apply (Cderiv_mul (fun _ => prodfac (takeN rho (S N)) C0)
           (fun w => Cexpf (Copp (Cmul w (Slist (takeN rho (S N)))))) z C0 d1);
    [ apply Cderiv_const | exact Hd1 ].
Qed.

Lemma Hcof_ptcont : forall rho Gseq, ZeroEnumG rho Gseq -> forall N,
  ptcont (Hcof rho Gseq N).
Proof.
  intros rho Gseq HZ N.
  exact (holo_ptcont (Hcof rho Gseq N) (fun z => Hcof_holo rho Gseq HZ N z)).
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  eventually zero-free on every disk                             *)
(* ----------------------------------------------------------------- *)
Theorem Hcof_ne0 : forall rho Gseq, ZeroEnumG rho Gseq ->
  forall R, 0 < R -> exists N0, forall N, (N0 <= N)%nat ->
    forall z, Cmod z < R -> Hcof rho Gseq N z <> C0.
Proof.
  intros rho Gseq HZ R HR.
  destruct HZ as [Hne [_ [_ Hfree]]].
  destruct (Hfree R HR) as [N0 HN0].
  exists N0. intros N HN z Hz. unfold Hcof.
  apply Cmul_ne0; [ apply Cmul_ne0 | ].
  - apply prodfac_ne0_notin. intro Hin.
    unfold takeN in Hin. apply in_map_iff in Hin.
    destruct Hin as [n [Hn _]]. exact (Hne n Hn).
  - apply Cexpf_ne0.
  - apply HN0; [ lia | exact Hz ].
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  off the zero set, Hcof is the naive quotient -- and converges  *)
(* ----------------------------------------------------------------- *)
Lemma Hcof_eq_Hseq : forall rho Gseq, ZeroEnumG rho Gseq -> forall N z,
  Pprod (fun k => Efac z (rho k)) N <> C0 ->
  Hcof rho Gseq N z = Hseq rho N z.
Proof.
  intros rho Gseq HZ N z Hne. unfold Hseq.
  rewrite (Hcof_id rho Gseq HZ N z). field. exact Hne.
Qed.

Theorem Hcof_cv_off : forall rho Gseq, ZeroEnumG rho Gseq ->
  (forall n, 1 <= Cmod (rho n)) ->
  forall z, (forall n, z <> rho n) ->
  forall P, CUn_cv (Pprod (fun k => Efac z (rho k))) P ->
  CUn_cv (fun N => Hcof rho Gseq N z) (Cmul (XiC z) (Cinv P)).
Proof.
  intros rho Gseq HZ Hlow z Hz P HP.
  assert (HZE : ZeroEnum rho) by (apply (ZeroEnumG_ZeroEnum rho Gseq HZ)).
  assert (Hfne : forall k, Efac z (rho k) <> C0).
  { intro k. apply Efac_ne0; [ | apply Hz ].
    intro Hc. pose proof (Hlow k) as Hl.
    rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hl. lra. }
  apply (CUn_cv_ext (fun N => Hseq rho N z)).
  - intro N. symmetry.
    apply Hcof_eq_Hseq; [ exact HZ | apply Pprod_ne0; exact Hfne ].
  - apply Hseq_cv; assumption.
Qed.

Print Assumptions Hcof_ne0.
Print Assumptions Hcof_cv_off.
