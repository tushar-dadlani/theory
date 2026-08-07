(* ================================================================= *)
(*  CVonMangoldtAbel.v  —  integral rep, brick IR1: the Abel identity   *)
(*  for the von Mangoldt Dirichlet series.                             *)
(*                                                                    *)
(*  With a_k = Lam k, c_k = k^{-s}, summation by parts (CAbelSummation) *)
(*  gives, since Cpsum(Lam) = psi and Lam 0 = 0,                        *)
(*     Cpsum (pterm s) M = psi(S M)*(S M)^{-s}                          *)
(*                         - Cabel_correction (RtoC.Lam) (gC s . INR) M,*)
(*  and each correction increment c_{k+1}-c_k = CgderivInt s k (k+1)    *)
(*  = Int_k^{k+1} (-s x^{-s-1}) dx (the C-valued FTC, CFTC).            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CAbelSummation CFTC
        CVonMangoldtSeries CDirichlet CZetaTerm VonMangoldtGlobal
        Chebyshev ChebyshevBound.
Open Scope R_scope.

(* ---- Cpsum of Lam is psi (Lam 0 = 0, psi_succ) ---- *)
Lemma sum_Lam_psi : forall N, sum_f_R0 Lam N = psi N.
Proof.
  induction N as [|N IH].
  - cbn [sum_f_R0]; rewrite psi_0; reflexivity.
  - rewrite tech5, IH, psi_succ; reflexivity.
Qed.

Lemma Cpsum_Lam_psi : forall N, Cpsum (fun k => RtoC (Lam k)) N = RtoC (psi N).
Proof.
  intro N; apply Ceq.
  - rewrite Re_Cpsum; unfold RtoC; cbn [Re]; apply sum_Lam_psi.
  - rewrite Im_Cpsum; unfold RtoC; cbn [Im]; rewrite sum_cte; ring.
Qed.

Section Abel.
Variable s : C.

(* ---- the Dirichlet partial sum as a (a_k c_k) sum ---- *)
Lemma Cpsum_ac_pterm : forall M,
  Cpsum (fun k => Cmul (RtoC (Lam k)) (gC s (INR k))) (S M) = Cpsum (pterm s) M.
Proof.
  induction M as [|M IH].
  - cbn [Cpsum].
    assert (HL0 : RtoC (Lam 0) = C0) by (unfold RtoC, C0; reflexivity).
    rewrite HL0; unfold pterm, cterm; ring.
  - change (Cpsum (fun k => Cmul (RtoC (Lam k)) (gC s (INR k))) (S (S M)))
      with (Cadd (Cpsum (fun k => Cmul (RtoC (Lam k)) (gC s (INR k))) (S M))
                 (Cmul (RtoC (Lam (S (S M)))) (gC s (INR (S (S M)))))).
    change (Cpsum (pterm s) (S M))
      with (Cadd (Cpsum (pterm s) M) (pterm s (S M))).
    rewrite IH; unfold pterm, cterm; reflexivity.
Qed.

(* ---- THE Abel identity ---- *)
Theorem phi_abel : forall M,
  Cpsum (pterm s) M
  = Cminus (Cmul (RtoC (psi (S M))) (gC s (INR (S M))))
           (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M).
Proof.
  intro M.
  transitivity (Cpsum (fun k => Cmul (RtoC (Lam k)) (gC s (INR k))) (S M)).
  { symmetry; apply Cpsum_ac_pterm. }
  pose proof (Cabel_summation' (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M) as HA.
  rewrite Cpsum_Lam_psi in HA.
  exact HA.
Qed.

(* ---- the correction increment is a cell integral (C-valued FTC) ---- *)
Lemma cell_increment : forall k (Hk : 0 < INR k) (Hkle : INR k <= INR (S k)),
  Cminus (gC s (INR (S k))) (gC s (INR k)) = CgderivInt s (INR k) (INR (S k)) Hk Hkle.
Proof. intros k Hk Hkle; symmetry; apply gC_FTC. Qed.

End Abel.

Print Assumptions phi_abel.

(* ================================================================= *)
(*  END CVonMangoldtAbel.v  —  Abel identity for Sum Lam(n) n^{-s}.     *)
(* ================================================================= *)
