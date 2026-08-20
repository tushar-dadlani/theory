(* ================================================================= *)
(*  XiHadamardOrderOne.v  —  the Hadamard factorization of xi,         *)
(*  reduced to ONE analytic hypothesis.                                *)
(*                                                                    *)
(*    xi_hadamard_factor : SubQuadLog Hglob ->                         *)
(*      exists A b, A <> C0 /\ forall z,                               *)
(*        xi z = A . e^{b z} . PROD_n (1 - z/rho_n) e^{z/rho_n}.       *)
(*                                                                    *)
(*  Everything else is discharged.  order_one_step_uncond asks for     *)
(*  five things about H; four are now free:                            *)
(*                                                                    *)
(*    H entire            -- Hglob_holo                                *)
(*    H' as a FUNCTION,   -- CDerivGlobal.Fderiv, the Cauchy tower at  *)
(*      itself entire        a radius read off the point               *)
(*    H nowhere zero      -- Hglob_ne0                                 *)
(*    H'/H path-continuous -- it is holomorphic (H is zero-free), so   *)
(*                            ptcont_CcontC applies                    *)
(*                                                                    *)
(*  The fifth, SubQuadLog H = "ln |H| is o(r^2)", is the one genuinely  *)
(*  analytic input left in the whole Hadamard programme.  It is TRUE    *)
(*  and in fact very slack -- H turns out to be A e^{bz}, so ln|H| is   *)
(*  O(r) -- but proving it is the classical minimum-modulus argument:   *)
(*  |H| = |xi| / |P| blows up at every zero of P, so the bound cannot   *)
(*  be read off pointwise.  One bounds |H| on a circle chosen to avoid  *)
(*  the zeros (pigeonhole on the O(r ln r) zeros in |z| <= 5r) and      *)
(*  carries it inward by the Cauchy integral formula.  That needs       *)
(*  SUM 1/|rho|^{3/2} < oo, which the counting function already         *)
(*  supports.  Stated here, not proved here.                            *)
(*                                                                    *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus Holomorphic CDeriv CHoloCcontC CHoloCalculus
        CexpFull PerronRemovable CSegInt CInfProd JensenMultiZero
        CZeroListFactor COrderOne CBorelBound CDerivGlobal
        RiemannXiEntire XiZeroEnum XiHadamardProd XiHcof XiTMHolo
        XiHadamardLocal XiHadamardGlue.
Open Scope R_scope.

Section OrderOne.

Variable rho : nat -> C.
Variable Gseq : nat -> C -> C.
Hypothesis HZ : ZeroEnumG rho Gseq.
Hypothesis Hlow : forall n, 1 <= Cmod (rho n).

Notation Hg := (Hglob rho Gseq HZ Hlow).

Lemma Hg_holo : forall z, exists d, is_Cderiv Hg z d.
Proof. exact (Hglob_holo rho Gseq HZ Hlow). Qed.

Lemma Hg_ptc : ptcont Hg.
Proof. exact (holo_ptcont Hg Hg_holo). Qed.

(* the derivative, as a function, and its holomorphy *)
Notation Hgp := (Fderiv Hg Hg_ptc).

Lemma Hgp_spec : forall z, is_Cderiv Hg z (Hgp z).
Proof. exact (Fderiv_spec Hg Hg_ptc Hg_holo). Qed.

Lemma Hgp_holo : forall z, exists d, is_Cderiv Hgp z d.
Proof. exact (Fderiv_holo Hg Hg_ptc Hg_holo). Qed.

(* the logarithmic derivative is holomorphic, hence path-continuous *)
Lemma Hlogd_cont : CcontC (fun w => Cmul (Hgp w) (Cinv (Hg w))).
Proof.
  apply ptcont_CcontC. apply holo_ptcont. intro z.
  destruct (Hgp_holo z) as [d1 Hd1].
  destruct (Hg_holo z) as [d2 Hd2].
  eexists. apply Cderiv_div;
    [ exact Hd1 | exact Hd2 | apply (Hglob_ne0 rho Gseq HZ Hlow) ].
Qed.

(* ----------------------------------------------------------------- *)
(*  THE FACTORIZATION                                                  *)
(* ----------------------------------------------------------------- *)
Theorem xi_hadamard_factor : SubQuadLog Hg ->
  exists A b : C, A <> C0 /\
    forall z, XiC z = Cmul (Cmul A (Cexpf (Cmul b z)))
                           (Pinf rho Gseq HZ Hlow z).
Proof.
  intro Hsq.
  destruct (order_one_step_uncond Hg Hgp Hgp_spec Hgp_holo
              (Hglob_ne0 rho Gseq HZ Hlow) Hlogd_cont Hsq)
    as [A [b [HA Hform]]].
  exists A, b. split; [ exact HA | ].
  intro z. rewrite <- (Hform z). apply (Hglob_id rho Gseq HZ Hlow z).
Qed.

End OrderOne.

Print Assumptions xi_hadamard_factor.
