(* ================================================================= *)
(*  XiHadamardLocal.v  —  PIECE 2, assembled.                          *)
(*                                                                    *)
(*    xi_hadamard_local : for every radius R there is an H, holomorphic *)
(*      and ZERO-FREE on Cmod z < R, with                               *)
(*                                                                    *)
(*        xi z = H z . P z          for all z in that disk,            *)
(*                                                                    *)
(*      P being the Hadamard product limit.                            *)
(*                                                                    *)
(*  H is not built as a limit of the cofactors Hcof N -- that route     *)
(*  needs |Hcof M| bounded on a closed disk, i.e. compactness.  It is   *)
(*  built outright:                                                    *)
(*                                                                    *)
(*      H := Hcof M . (T_M)^{-1},                                      *)
(*                                                                    *)
(*  for one M chosen to serve two masters at once: past Hcof_ne0's     *)
(*  threshold so Hcof M is zero-free on the disk, and past Msel so the  *)
(*  tail product never drops below 1/2 there (XiTMSelect.TM_ne0_disk).  *)
(*  A Nat.max of the two; raising the index is free because Ttl is      *)
(*  decreasing.                                                        *)
(*                                                                    *)
(*  WHY LOCAL AND NOT GLOBAL.  At a far zero rho_k (k > M) BOTH factors *)
(*  vanish -- Hcof M does because xi does and Pprod M does not, and     *)
(*  T_M does by definition -- so Hcof M . (T_M)^{-1} evaluates to       *)
(*  C0 . C0 = C0 there rather than to the true nonzero value.  The      *)
(*  representation is therefore valid exactly where T_M has no zeros,   *)
(*  which is the disk.  Gluing the H's across radii into one entire     *)
(*  function is a separate step: they agree off the zeros, both being   *)
(*  xi/P there.                                                        *)
(*                                                                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CIntegral2 CSegInt
        CSeries CInfProd CDyadicSum JensenMultiZero CZeroListFactor
        RiemannXiEntire XiZeroEnum XiHgrow XiHadamardProd XiHadamardUnif
        XiProdFactor XiProdLimit XiHcof XiTailProd XiTMHolo XiTMSelect
        CHoloCalculus.
Open Scope R_scope.

Lemma CUn_cv_shift : forall (u : nat -> C) (l : C) (M : nat),
  CUn_cv u l -> CUn_cv (fun k => u (S (M + k))) l.
Proof.
  intros u l M Hcv eps Heps. destruct (Hcv eps Heps) as [N HN].
  exists N. intros k Hk. apply HN. lia.
Qed.

Section Assembly.

Variable rho : nat -> C.
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Definition HE : ZeroEnum rho := ZeroEnumG_ZeroEnum rho Gseq HZ.

(* the Hadamard product, as a function *)
Definition Pinf (z : C) : C := proj1_sig (hadamard_prod_cv rho HE Hlow z).

Lemma Pinf_spec : forall z, CUn_cv (Pprod (fun k => Efac z (rho k))) (Pinf z).
Proof. intro z. exact (proj2_sig (hadamard_prod_cv rho HE Hlow z)). Qed.

(* the product splits at M into head times tail *)
Lemma Pinf_split : forall M z,
  Pinf z = Cmul (Pprod (fun k => Efac z (rho k)) M) (TM rho HE Hlow M z).
Proof.
  intros M z.
  assert (Hsub : CUn_cv (fun k => Pprod (fun k' => Efac z (rho k')) (S (M + k)))
                        (Pinf z))
    by (apply CUn_cv_shift; apply Pinf_spec).
  assert (Hsplit : CUn_cv (fun k => Cmul (Pprod (fun k' => Efac z (rho k')) M)
                                         (Pprod (fun j => Efac z (rsh rho M j)) k))
                          (Pinf z)).
  { apply (CUn_cv_ext (fun k => Pprod (fun k' => Efac z (rho k')) (S (M + k))));
      [ intro k; apply Pprod_split | exact Hsub ]. }
  assert (Hlim : CUn_cv (fun k => Cmul (Pprod (fun k' => Efac z (rho k')) M)
                                       (Pprod (fun j => Efac z (rsh rho M j)) k))
                        (Cmul (Pprod (fun k' => Efac z (rho k')) M)
                              (TM rho HE Hlow M z)))
    by (apply CUn_cv_scal; apply TM_spec).
  exact (CUn_cv_unique _ _ _ Hsplit Hlim).
Qed.

(* ================================================================= *)
(*  THE ASSEMBLY                                                       *)
(* ================================================================= *)
Theorem xi_hadamard_local : forall R, 0 < R ->
  exists H : C -> C,
    (forall z, Cmod z < R -> exists d, is_Cderiv H z d) /\
    (forall z, Cmod z < R -> H z <> C0) /\
    (forall z, Cmod z < R -> XiC z = Cmul (H z) (Pinf z)).
Proof.
  intros R HR.
  (* threshold 1: Hcof N is zero-free on the disk *)
  destruct (Hcof_ne0 rho Gseq HZ R HR) as [N0 HN0].
  (* threshold 2: past Msel, the tail product never drops below 1/2 *)
  set (M := Nat.max N0 (Msel rho HE Hlow R)).
  assert (HMN0 : (N0 <= M)%nat) by (unfold M; lia).
  assert (HTMne : forall z, Cmod z < R -> TM rho HE Hlow M z <> C0).
  { intros z Hz. apply (TM_ne0_disk rho HE Hlow R HR M); [ | exact Hz ].
    pose proof (Msel_spec rho HE Hlow R HR) as Hs.
    pose proof (Ttl_decr rho HE Hlow (Msel rho HE Hlow R) M
                  ltac:(unfold M; lia)) as Hd.
    pose proof (KR_pos R HR) as HK. nra. }
  (* the cofactor *)
  exists (fun z => Cmul (Hcof rho Gseq M z) (Cinv (TM rho HE Hlow M z))).
  split; [ | split ].
  - (* holomorphic on the disk *)
    intros z Hz.
    destruct (Hcof_holo rho Gseq HZ M z) as [d1 Hd1].
    destruct (TM_holo rho HE Hlow M z) as [d2 Hd2].
    eexists. apply Cderiv_div; [ exact Hd1 | exact Hd2 | apply HTMne; exact Hz ].
  - (* zero-free on the disk *)
    intros z Hz. apply Cmul_ne0.
    + apply (HN0 M HMN0 z Hz).
    + intro Hc.
      assert (Hone : Cmul (TM rho HE Hlow M z) (Cinv (TM rho HE Hlow M z)) = C1)
        by (field; apply HTMne; exact Hz).
      rewrite Hc in Hone.
      assert (Hz0 : Cmul (TM rho HE Hlow M z) C0 = C0) by ring.
      rewrite Hz0 in Hone. exact (C1_neq_C0 (eq_sym Hone)).
  - (* the identity *)
    intros z Hz.
    rewrite (Hcof_id rho Gseq HZ M z), (Pinf_split M z).
    field. apply HTMne; exact Hz.
Qed.

End Assembly.

Print Assumptions xi_hadamard_local.
