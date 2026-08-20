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
(*  for one M chosen to serve three masters at once: past Hcof_ne0's    *)
(*  threshold so Hcof M is zero-free on the disk; past the escape       *)
(*  clause's threshold for radius R so every remaining rho_k lies       *)
(*  OUTSIDE the disk; and far enough out that exp(KR R . Ttl M) - 1     *)
(*  <= 1/2, so the tail product never drops below 1/2 there.  A Nat.max *)
(*  of three indices, with the third coming from Ttl -> 0 and the same  *)
(*  exp_m1_le device used throughout.                                  *)
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
        XiProdFactor XiProdLimit XiHcof XiTailProd XiTMHolo CHoloCalculus.
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
  pose proof (exp_pos 1) as Hp1.
  assert (HKR : 0 < KR R).
  { unfold KR. pose proof (exp_pos R) as HeR.
    apply Rmult_lt_0_compat; [ nra | ].
    assert (0 < 3 * (1 + R) * exp R) by (apply Rmult_lt_0_compat; nra). lra. }
  (* threshold 1: Hcof N is zero-free on the disk *)
  destruct (Hcof_ne0 rho Gseq HZ R HR) as [N0 HN0].
  (* threshold 2: the tail product never drops below 1/2 *)
  set (u0 := Rmin 1 (/ (2 * exp 1))).
  assert (Hu0 : 0 < u0)
    by (apply Rmin_glb_lt; [ lra | apply Rinv_0_lt_compat; lra ]).
  destruct (Ttl_small rho HE Hlow (u0 / KR R)
              ltac:(apply Rdiv_lt_0_compat; lra)) as [N1 HN1].
  set (M := Nat.max N0 N1).
  assert (HMN0 : (N0 <= M)%nat) by (unfold M; lia).
  assert (HMN1 : (N1 <= M)%nat) by (unfold M; lia).
  assert (Htl : KR R * Ttl rho HE Hlow M < u0).
  { pose proof (Ttl_decr rho HE Hlow N1 M HMN1) as Hd.
    assert (Hlt : Ttl rho HE Hlow M < u0 / KR R) by lra.
    apply (Rmult_lt_reg_r (/ KR R)); [ apply Rinv_0_lt_compat; lra | ].
    replace (KR R * Ttl rho HE Hlow M * / KR R) with (Ttl rho HE Hlow M)
      by (field; lra).
    replace (u0 * / KR R) with (u0 / KR R) by (unfold Rdiv; ring). exact Hlt. }
  assert (Htl0 : 0 <= KR R * Ttl rho HE Hlow M).
  { pose proof (Ttl_nonneg rho HE Hlow M). nra. }
  assert (Hhalf : exp (KR R * Ttl rho HE Hlow M) - 1 <= / 2).
  { set (u := KR R * Ttl rho HE Hlow M).
    assert (H1 : u <= 1) by (pose proof (Rmin_l 1 (/ (2 * exp 1)));
                             unfold u0 in Htl; unfold u; lra).
    assert (H2 : u < / (2 * exp 1)) by (pose proof (Rmin_r 1 (/ (2 * exp 1)));
                                        unfold u0 in Htl; unfold u; lra).
    pose proof (exp_m1_le u Htl0) as He.
    assert (Hexp1 : exp u <= exp 1) by (apply exp_le; exact H1).
    assert (Hu : 0 <= u) by exact Htl0.
    assert (Hs1 : u * exp u <= u * exp 1) by (apply Rmult_le_compat_l; lra).
    assert (Hs2 : u * exp 1 < / (2 * exp 1) * exp 1)
      by (apply Rmult_lt_compat_r; lra).
    assert (Hkey : / (2 * exp 1) * exp 1 = / 2) by (field; lra).
    lra. }
  (* so the tail product is bounded below on the disk, hence T_M <> 0 there *)
  assert (HTMne : forall z, Cmod z < R -> TM rho HE Hlow M z <> C0).
  { intros z Hz.
    assert (Hge : forall k, / 2 <= Cmod (Pprod (fun j => Efac z (rsh rho M j)) k))
      by (intro k; apply (tail_prod_ge rho HE Hlow R HR M Hhalf z ltac:(lra) k)).
    assert (Hlim : / 2 <= Cmod (TM rho HE Hlow M z))
      by (apply (CUn_cv_mod_ge _ _ (/ 2) 0%nat (TM_spec rho HE Hlow M z));
          intros n _; apply Hge).
    intro Hc. rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hlim. lra. }
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
