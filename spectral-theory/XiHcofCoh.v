(* ================================================================= *)
(*  XiHcofCoh.v  —  the glue, part 1: the cofactors cohere.            *)
(*                                                                    *)
(*    Hcof_coh : Hcof M z = Hcof N z . Q z   for ALL z, N = S(M+k),    *)
(*      Q the block of Weierstrass factors between M and N;            *)
(*    TM_split : TM M z = Q z . TM N z, the same block;                *)
(*    Hcof_TM_indep : Hcof M z . (TM M z)^{-1} is INDEPENDENT of M,    *)
(*      over all M for which TM M z <> C0.                             *)
(*                                                                    *)
(*  The third is what makes a global H possible.  The local theorem    *)
(*  had to pick an M by radius; if the value depended on that choice   *)
(*  the local functions would not patch.  They do, and the reason is   *)
(*  that the SAME block Q appears in both factorizations -- of xi by   *)
(*  Hcof_coh, and of the tail product by TM_split -- so it cancels.    *)
(*                                                                    *)
(*  Hcof_coh cannot be proved by algebra alone.  Gseq M and Gseq N are *)
(*  tied to each other only through xi, so extracting the relation      *)
(*  means dividing by prod_{j<=M} Efac z (rho j), which vanishes at     *)
(*  the first M+1 zeros.  CFiniteCancel.ptcont_eq_off_finite covers     *)
(*  those points by continuity; that is the only analysis here.        *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC CGoursatConv
        CSeries CInfProd JensenMultiZero CZeroListFactor CFiniteCancel
        RiemannXiEntire XiZeroEnum XiHadamardProd XiProdFactor XiProdLimit
        XiHcof XiTailProd XiTMHolo.
Open Scope R_scope.

Lemma CUn_cv_shiftk : forall (u : nat -> C) (l : C) (k : nat),
  CUn_cv u l -> CUn_cv (fun i => u (S (k + i))) l.
Proof.
  intros u l k Hcv eps Heps. destruct (Hcv eps Heps) as [N HN].
  exists N. intros i Hi. apply HN. lia.
Qed.

Lemma Pprod_ext : forall (f g : nat -> C) (n : nat),
  (forall j, f j = g j) -> Pprod f n = Pprod g n.
Proof.
  intros f g n Heq. induction n as [| n IH]; cbn [Pprod];
    [ apply Heq | rewrite IH, Heq; reflexivity ].
Qed.

Lemma Pprod_ne0_le : forall (f : nat -> C) (N : nat),
  (forall k, (k <= N)%nat -> f k <> C0) -> Pprod f N <> C0.
Proof.
  intros f N Hf. induction N as [| N IH]; cbn [Pprod].
  - apply Hf; lia.
  - apply Cmul_ne0; [ apply IH; intros k Hk; apply Hf; lia | apply Hf; lia ].
Qed.

(* the block of factors strictly between index M and index S(M+k) *)
Definition Qblk (rho : nat -> C) (M k : nat) (z : C) : C :=
  Pprod (fun j => Efac z (rho (S (M + j)))) k.

Lemma Qblk_holo : forall rho M k z, exists d, is_Cderiv (Qblk rho M k) z d.
Proof. intros rho M k z. exact (Pprod_Efac_holo (fun j => rho (S (M + j))) k z). Qed.

(* ----------------------------------------------------------------- *)
(*  A.  xi's cofactors cohere                                          *)
(* ----------------------------------------------------------------- *)
Theorem Hcof_coh : forall rho Gseq, ZeroEnumG rho Gseq -> forall M k z,
  Hcof rho Gseq M z
  = Cmul (Hcof rho Gseq (S (M + k)) z) (Qblk rho M k z).
Proof.
  intros rho Gseq HZ M k.
  assert (Hne : forall n, rho n <> C0) by (destruct HZ as [H _]; exact H).
  apply (ptcont_eq_off_finite (takeN rho (S M))).
  - exact (Hcof_ptcont rho Gseq HZ M).
  - assert (Hh : forall z, exists d,
             is_Cderiv (fun w => Cmul (Hcof rho Gseq (S (M + k)) w) (Qblk rho M k w)) z d).
    { intro z.
      destruct (Hcof_holo rho Gseq HZ (S (M + k)) z) as [d1 Hd1].
      destruct (Qblk_holo rho M k z) as [d2 Hd2].
      eexists. apply Cderiv_mul; [ exact Hd1 | exact Hd2 ]. }
    exact (holo_ptcont _ Hh).
  - intros z Hnotin.
    (* off the first M+1 zeros the head product is invertible *)
    assert (Hhead : Pprod (fun j => Efac z (rho j)) M <> C0).
    { apply Pprod_ne0_le. intros j Hj. apply Efac_ne0; [ apply Hne | ].
      intro Hc. apply Hnotin. rewrite Hc. unfold takeN.
      apply in_map_iff. exists j. split; [ reflexivity | apply in_seq; lia ]. }
    apply (Cmul_cancel_l (Pprod (fun j => Efac z (rho j)) M)); [ exact Hhead | ].
    pose proof (Hcof_id rho Gseq HZ M z) as HidM.
    pose proof (Hcof_id rho Gseq HZ (S (M + k)) z) as HidN.
    rewrite (Pprod_split (fun j => Efac z (rho j)) M k) in HidN.
    assert (Hq : Pprod (fun j => Efac z (rho (S (M + j)))) k = Qblk rho M k z)
      by reflexivity.
    rewrite Hq in HidN.
    (* HidM :  xi z = Hcof M z . Pprod M                                *)
    (* HidN :  xi z = Hcof N z . (Pprod M . Qblk)                       *)
    transitivity (XiC z); [ rewrite HidM; ring | rewrite HidN; ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the tail product splits at the same place                      *)
(* ----------------------------------------------------------------- *)
Section Split.

Variable rho : nat -> C.
Hypothesis Henum : ZeroEnum rho.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Lemma TM_split : forall M k z,
  TM rho Henum Hlow M z
  = Cmul (Qblk rho M k z) (TM rho Henum Hlow (S (M + k)) z).
Proof.
  intros M k z.
  assert (Hsub : CUn_cv (fun i => Pprod (fun j => Efac z (rsh rho M j)) (S (k + i)))
                        (TM rho Henum Hlow M z))
    by (apply CUn_cv_shiftk; apply TM_spec).
  assert (Hre : forall i,
            Pprod (fun j => Efac z (rsh rho M j)) (S (k + i))
            = Cmul (Qblk rho M k z)
                   (Pprod (fun j => Efac z (rsh rho (S (M + k)) j)) i)).
  { intro i. rewrite (Pprod_split (fun j => Efac z (rsh rho M j)) k i).
    unfold Qblk, rsh. f_equal; apply Pprod_ext; intro j;
      first [ reflexivity
            | replace (S (M + S (k + j)))%nat with (S (S (M + k) + j))%nat by lia;
              reflexivity ]. }
  assert (Hcv : CUn_cv (fun i => Cmul (Qblk rho M k z)
                          (Pprod (fun j => Efac z (rsh rho (S (M + k)) j)) i))
                       (TM rho Henum Hlow M z))
    by (apply (CUn_cv_ext _ _ _ Hre) in Hsub; exact Hsub).
  assert (Hlim : CUn_cv (fun i => Cmul (Qblk rho M k z)
                          (Pprod (fun j => Efac z (rsh rho (S (M + k)) j)) i))
                        (Cmul (Qblk rho M k z) (TM rho Henum Hlow (S (M + k)) z)))
    by (apply CUn_cv_scal; apply TM_spec).
  exact (CUn_cv_unique _ _ _ Hcv Hlim).
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  M-independence                                                 *)
(* ----------------------------------------------------------------- *)
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.

Lemma Hcof_TM_step : forall M k z,
  TM rho Henum Hlow M z <> C0 ->
  Cmul (Hcof rho Gseq M z) (Cinv (TM rho Henum Hlow M z))
  = Cmul (Hcof rho Gseq (S (M + k)) z)
         (Cinv (TM rho Henum Hlow (S (M + k)) z)).
Proof.
  intros M k z Hne.
  pose proof (TM_split M k z) as Hsp.
  assert (HQ : Qblk rho M k z <> C0)
    by (intro Hc; apply Hne; rewrite Hsp, Hc; ring).
  assert (HN : TM rho Henum Hlow (S (M + k)) z <> C0)
    by (intro Hc; apply Hne; rewrite Hsp, Hc; ring).
  rewrite (Hcof_coh rho Gseq HZ M k z), Hsp. field. split; assumption.
Qed.

Theorem Hcof_TM_indep : forall M N z,
  TM rho Henum Hlow M z <> C0 ->
  TM rho Henum Hlow N z <> C0 ->
  Cmul (Hcof rho Gseq M z) (Cinv (TM rho Henum Hlow M z))
  = Cmul (Hcof rho Gseq N z) (Cinv (TM rho Henum Hlow N z)).
Proof.
  (* both sides agree with the value at max M N *)
  assert (Hup : forall M N z, (M <= N)%nat ->
            TM rho Henum Hlow M z <> C0 ->
            Cmul (Hcof rho Gseq M z) (Cinv (TM rho Henum Hlow M z))
            = Cmul (Hcof rho Gseq N z) (Cinv (TM rho Henum Hlow N z))).
  { intros M N z HMN HneM. destruct (Nat.eq_dec M N) as [He | He].
    - rewrite He. reflexivity.
    - assert (Hk : exists k, N = S (M + k)) by (exists (N - S M)%nat; lia).
      destruct Hk as [k Hk]. rewrite Hk. apply Hcof_TM_step; exact HneM. }
  intros M N z HM HN.
  destruct (Nat.le_ge_cases M N) as [Hle | Hge].
  - apply Hup; assumption.
  - symmetry. apply Hup; assumption.
Qed.

End Split.

Print Assumptions Hcof_coh.
Print Assumptions Hcof_TM_indep.
