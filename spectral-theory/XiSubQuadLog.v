(* ================================================================= *)
(*  XiSubQuadLog.v  —  SubQuadLog Hglob, and the Hadamard             *)
(*  factorization of xi made UNCONDITIONAL.                            *)
(*                                                                    *)
(*    xi_subquadlog     : SubQuadLog (Hglob rho Gseq HZ Hlow)          *)
(*    xi_hadamard_final : exists A b, A <> C0 /\                       *)
(*        xi z = A . e^{b z} . PROD_n (1 - z/rho_n) e^{z/rho_n}        *)
(*                                                                    *)
(*  This closes the chain COrderOne left open when it isolated         *)
(*  SubQuadLog as the one analytic hypothesis of the order-1 step.     *)
(*  Everything else was discharged earlier: BorelCaratheodory by       *)
(*  CBorelBound, the derivative-as-a-function by CDerivGlobal, the     *)
(*  zero-freeness and the product identity by XiHadamardGlue.          *)
(*                                                                    *)
(*  Mf is assembled, not derived.  Its three obligations -- monotone,  *)
(*  dominating, o(r^2) -- are each closed under sum, so the majorant   *)
(*  is built piecewise and no global constant is ever named:           *)
(*                                                                    *)
(*      Mf t = ln 4 + Lxi (4 msh t) + Cu . msh t . ln^2 (msh t)        *)
(*                                                                    *)
(*  with msh t = max t 0 + Rbase.  The max is not cosmetic: SubQuadLog *)
(*  asks for monotonicity on ALL of R, while Lxi genuinely dips below  *)
(*  t = PI - 1, so the argument has to be held clear of the origin.    *)
(*  Rbase = 2700 + |ln M0| is the least shift that satisfies every     *)
(*  threshold the estimates accumulated: 8 for the disk bound, 80 for  *)
(*  the log-scaling, 648 for Bub, and |ln M0| + 2601 for the nested    *)
(*  logarithm in negLBexp_bound.                                       *)
(*                                                                    *)
(*  Note what is still hypothetical: ZeroEnumG.  The factorization is  *)
(*  unconditional GIVEN an enumeration of the zeros with its cofactor  *)
(*  family, and producing one is the choice-flavoured gap recorded in  *)
(*  XiZeroEnum -- untouched here.  Axiom-clean.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv CexpFull CSegInt
        COrderOne CBorelBound RLogPower RSubQuad
        JensenMultiZero CZeroListFactor RiemannXiEntire
        XiZeroCount XiZeroDensity XiHgrow XiZeroEnum XiHadamardProd
        XiHcof XiProdLimit XiHadamardLocal XiHadamardGlue XiHadamardOrderOne
        XiProdLower XiLnBound XiLxiMajor XiBubBound XiHDiskBound.
Open Scope R_scope.

Definition msh (t : R) : R := Rmax t 0 + Rbase.

Lemma Rbase_ge : 2700 <= Rbase.
Proof. unfold Rbase. pose proof (Rabs_pos (ln M0)). lra. Qed.

Lemma msh_ge : forall t, Rbase <= msh t.
Proof. intro t. unfold msh. pose proof (Rmax_r t 0). lra. Qed.

Lemma msh_mono : forall a b, a <= b -> msh a <= msh b.
Proof.
  intros a b Hab. unfold msh.
  assert (Rmax a 0 <= Rmax b 0)
    by (apply Rmax_lub; [ apply Rle_trans with b; [ exact Hab | apply Rmax_l ]
                        | apply Rmax_r ]).
  lra.
Qed.

Lemma msh_id : forall t, 0 <= t -> msh t = t + Rbase.
Proof. intros t Ht. unfold msh. rewrite Rmax_left by lra. reflexivity. Qed.

Definition Mf (t : R) : R :=
  ln 4 + Lxi (4 * msh t) + Cu * (msh t * (ln (msh t)) ^ 2).

Lemma Cu_nonneg : 0 <= Cu.
Proof.
  unfold Cu. pose proof (Rabs_pos (ln M0)). pose proof agrow_nonneg. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  A.  Mf is monotone                                                 *)
(* ----------------------------------------------------------------- *)
Lemma Mf_mono : forall a b, a <= b -> Mf a <= Mf b.
Proof.
  intros a b Hab. unfold Mf.
  pose proof Rbase_ge as HR. pose proof (msh_ge a) as Ha. pose proof (msh_ge b) as Hb.
  pose proof (msh_mono a b Hab) as Hm.
  pose proof Cu_nonneg as HCu.
  assert (H1 : Lxi (4 * msh a) <= Lxi (4 * msh b)) by (apply Lxi_mono; lra).
  assert (Hlna : 1 <= ln (msh a)) by (apply ln_ge1; lra).
  assert (Hlnb : ln (msh a) <= ln (msh b)) by (apply ln_mono_le; lra).
  assert (Hsq : (ln (msh a)) ^ 2 <= (ln (msh b)) ^ 2) by nra.
  assert (H2 : msh a * (ln (msh a)) ^ 2 <= msh b * (ln (msh b)) ^ 2)
    by (apply Rmult_le_compat; nra).
  assert (H3 : Cu * (msh a * (ln (msh a)) ^ 2)
               <= Cu * (msh b * (ln (msh b)) ^ 2))
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  Mf is o(r^2)                                                   *)
(* ----------------------------------------------------------------- *)
Lemma Mf_subquad : SubQuad Mf.
Proof.
  unfold Mf.
  apply SubQuad_plus; [ apply SubQuad_plus; [ apply SubQuad_const | ] | ].
  - (* the Lxi piece *)
    apply (SubQuad_le (fun t => Lxi (4 * msh t))
             (fun r => ln M0 + 40 * (r * (ln r) ^ 2))).
    + apply SubQuad_plus; [ apply SubQuad_const | ].
      apply SubQuad_scal; [ lra | apply SubQuad_rln2 ].
    + exists Rbase. intros r Hr.
      pose proof Rbase_ge as HRb.
      rewrite (msh_id r ltac:(lra)).
      pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
      assert (Hle : 4 * (r + Rbase) <= 8 * r) by lra.
      pose proof (Lxi_le (4 * (r + Rbase)) ltac:(lra)) as HL.
      assert (Hln8 : ln (4 * (r + Rbase)) <= 2 * ln r).
      { apply Rle_trans with (ln (8 * r));
          [ apply ln_mono_le; lra | apply ln_scal_le; lra ]. }
      assert (Hln0 : 0 <= ln (4 * (r + Rbase)))
        by (rewrite <- ln_1; apply ln_mono_le; lra).
      assert (Hpr : 4 * (r + Rbase) * ln (4 * (r + Rbase)) <= 8 * r * (2 * ln r))
        by (apply Rmult_le_compat; lra).
      assert (Hs1 : ln r <= r * (ln r) ^ 2) by nra.
      assert (Hs2 : r * ln r <= r * (ln r) ^ 2) by nra.
      lra.
  - (* the r ln^2 r piece *)
    apply (SubQuad_le (fun t => Cu * (msh t * (ln (msh t)) ^ 2))
             (fun r => (8 * Cu) * (r * (ln r) ^ 2))).
    + apply SubQuad_scal; [ pose proof Cu_nonneg; lra | apply SubQuad_rln2 ].
    + exists Rbase. intros r Hr.
      pose proof Rbase_ge as HRb. pose proof Cu_nonneg as HCu.
      rewrite (msh_id r ltac:(lra)).
      pose proof (ln_ge1 r ltac:(lra)) as Hlnr.
      assert (Hle : r + Rbase <= 2 * r) by lra.
      assert (Hln2 : ln (r + Rbase) <= 2 * ln r).
      { apply Rle_trans with (ln (2 * r));
          [ apply ln_mono_le; lra | apply ln_scal_le; lra ]. }
      assert (Hln0 : 0 <= ln (r + Rbase))
        by (rewrite <- ln_1; apply ln_mono_le; lra).
      assert (Hsq : (ln (r + Rbase)) ^ 2 <= 4 * (ln r) ^ 2) by nra.
      assert (Hpr : (r + Rbase) * (ln (r + Rbase)) ^ 2 <= 2 * r * (4 * (ln r) ^ 2))
        by (apply Rmult_le_compat; nra).
      assert (Hfin : Cu * ((r + Rbase) * (ln (r + Rbase)) ^ 2)
                     <= Cu * (2 * r * (4 * (ln r) ^ 2)))
        by (apply Rmult_le_compat_l; lra).
      lra.
Qed.

Section Final.

Variable rho : nat -> C.
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Notation Hg := (Hglob rho Gseq HZ Hlow).

(* ----------------------------------------------------------------- *)
(*  C.  Mf dominates ln |H|                                            *)
(* ----------------------------------------------------------------- *)
Lemma Mf_dominates : forall z, ln (Cmod (Hg z)) <= Mf (Cmod z).
Proof.
  intro z. pose proof Rbase_ge as HRb.
  pose proof (Cmod_nonneg z) as Hz0.
  set (r := Cmod z + Rbase).
  assert (Hr : Rbase <= r) by (unfold r; lra).
  assert (Hr8 : 8 <= r) by lra.
  destruct (xi_H_disk_bound rho Gseq HZ Hlow r Hr8)
    as [rr [del [K [Hlo [Hhi [Hd0 [Hdr [Hdb [HK1 [HK2 Hbd]]]]]]]]]].
  assert (Hzr : Cmod z <= r) by (unfold r; lra).
  pose proof (Hbd z Hzr) as Hln.
  (* size the two pieces *)
  assert (HL : Lxi rr <= Lxi (4 * r)) by (apply Lxi_mono; lra).
  pose proof (negLBexp_bound r rr del K Hr Hlo Hhi Hd0 Hdr Hdb HK1 HK2) as HU.
  unfold Mf. rewrite (msh_id (Cmod z) Hz0). fold r. lra.
Qed.

Theorem xi_subquadlog : SubQuadLog Hg.
Proof.
  exists Mf. split; [ exact Mf_mono | ]. split; [ exact Mf_dominates | ].
  exact Mf_subquad.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  the factorization, no longer conditional                       *)
(* ----------------------------------------------------------------- *)
Theorem xi_hadamard_final :
  exists A b : C, A <> C0 /\
    forall z, XiC z = Cmul (Cmul A (Cexpf (Cmul b z)))
                           (Pinf rho Gseq HZ Hlow z).
Proof.
  exact (xi_hadamard_factor rho Gseq HZ Hlow xi_subquadlog).
Qed.

End Final.

Print Assumptions xi_subquadlog.
Print Assumptions xi_hadamard_final.
