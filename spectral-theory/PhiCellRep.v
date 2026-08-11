(* ================================================================= *)
(*  PhiCellRep.v  —  Newman A3: the Phi-side cell representation.         *)
(*                                                                    *)
(*  Ties the u-space cell machinery to phi_integral_rep.  The Abel        *)
(*  correction IS the psi-weighted sum of gC-increments (correction_      *)
(*  cells), each increment gC s(N+1)-gC s(N) is the cell integral of      *)
(*  gderivC = d/du u^{-s} (gC_FTC).  Hence:                              *)
(*                                                                    *)
(*    phi_incr_rep   : -sum_{k<=M} psi(k)(gC s(k+1)-gC s(k)) -> Phi s,     *)
(*    phi_cellint_rep: -sum_{k<=M} psi(k+1) int_{k+1}^{k+2} gderivC s      *)
(*                     -> Phi s   (the psiR-Stieltjes integral form).     *)
(*                                                                    *)
(*  This is the Phi-half of the Newman identity g=Phi(z+1)/(z+1)-1/z,     *)
(*  in u-space.  Axiom-clean.                                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CIntegral2 CSegInt
        CZetaTerm CFTC CAbelSummation CVonMangoldtIntegral CVonMangoldtSeries
        Chebyshev ChebyshevBound VonMangoldtGlobal.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  small helpers on complex sequences and partial sums                *)
(* ----------------------------------------------------------------- *)

Lemma CUn_cv_ext : forall u v l, (forall n, u n = v n) -> CUn_cv u l -> CUn_cv v l.
Proof.
  intros u v l Heq H eps He; destruct (H eps He) as [N HN];
    exists N; intros n Hn; rewrite <- (Heq n); apply HN; exact Hn.
Qed.

Lemma CUn_cv_shift1 : forall u l, CUn_cv u l -> CUn_cv (fun k => u (S k)) l.
Proof.
  intros u l H eps He; destruct (H eps He) as [N HN]; exists N; intros n Hn; apply HN; lia.
Qed.

Lemma Cpsum_ext : forall (f g : nat -> C) N, (forall k, f k = g k) -> Cpsum f N = Cpsum g N.
Proof. intros f g N Heq; induction N as [|N IH]; simpl; rewrite ?IH, ?Heq; reflexivity. Qed.

Lemma Cpsum_shift1 : forall (f : nat -> C) M,
  Cpsum f (S M) = Cadd (f O) (Cpsum (fun k => f (S k)) M).
Proof.
  intros f M; induction M as [|M IH]; [ reflexivity | ].
  change (Cpsum f (S (S M))) with (Cadd (Cpsum f (S M)) (f (S (S M)))).
  change (Cpsum (fun k => f (S k)) (S M))
    with (Cadd (Cpsum (fun k => f (S k)) M) (f (S (S M)))).
  rewrite IH; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  each gC increment is the cell integral of gderivC (u >= 1)          *)
(* ----------------------------------------------------------------- *)

Lemma cellpos : forall k, 0 < INR (S k).
Proof. intro k; apply lt_0_INR; lia. Qed.

Lemma cellle : forall k, INR (S k) <= INR (S (S k)).
Proof. intro k; apply le_INR; lia. Qed.

Lemma cell_incr_int : forall s k,
  Cminus (gC s (INR (S (S k)))) (gC s (INR (S k)))
  = CgderivInt s (INR (S k)) (INR (S (S k))) (cellpos k) (cellle k).
Proof. intros s k; symmetry; apply gC_FTC. Qed.

(* ----------------------------------------------------------------- *)
(*  the Phi-side representations                                        *)
(* ----------------------------------------------------------------- *)

(*  the psi-weighted gC-increment (Stieltjes) sum represents Phi  *)
Theorem phi_incr_rep : forall s (H : 1 < Re s),
  CUn_cv (fun M => Copp (Cpsum (fun k =>
            Cmul (RtoC (psi k)) (Cminus (gC s (INR (S k))) (gC s (INR k)))) M))
         (Phi s H).
Proof.
  intros s H.
  apply (CUn_cv_ext (fun M =>
    Copp (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M)));
    [ intro M; rewrite correction_cells; reflexivity | apply phi_integral_rep ].
Qed.

(*  the same, with each increment written as a cell integral of gderivC   *)
(*  (the k=0 term vanishes since psi 0 = 0, so the sum reindexes to k>=1)  *)
Theorem phi_cellint_rep : forall s (H : 1 < Re s),
  CUn_cv (fun M => Copp (Cpsum (fun k =>
            Cmul (RtoC (psi (S k)))
                 (CgderivInt s (INR (S k)) (INR (S (S k))) (cellpos k) (cellle k))) M))
         (Phi s H).
Proof.
  intros s H.
  apply (CUn_cv_ext (fun M =>
    Copp (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) (S M)))).
  - intro M; f_equal.
    rewrite correction_cells, Cpsum_shift1.
    replace (Cmul (RtoC (psi 0)) (Cminus (gC s (INR (S O))) (gC s (INR O)))) with C0
      by (rewrite psi_0; unfold RtoC, Cmul, C0; apply Ceq; cbn; ring).
    rewrite (Cpsum_ext
      (fun k => Cmul (RtoC (psi (S k))) (Cminus (gC s (INR (S (S k)))) (gC s (INR (S k)))))
      (fun k => Cmul (RtoC (psi (S k)))
                  (CgderivInt s (INR (S k)) (INR (S (S k))) (cellpos k) (cellle k))) M)
      by (intro k; rewrite cell_incr_int; reflexivity).
    ring.
  - apply (CUn_cv_shift1 (fun M =>
      Copp (Cabel_correction (fun k => RtoC (Lam k)) (fun k => gC s (INR k)) M)));
      apply phi_integral_rep.
Qed.

Print Assumptions phi_incr_rep.
Print Assumptions phi_cellint_rep.

(* ================================================================= *)
(*  END PhiCellRep.v — Phi as the psiR-weighted cell-integral sum.        *)
(*  With s = z+1 this is int_1^oo psiR(u) u^{-s-1} du = Phi(s)/s scaled     *)
(*  by -s (gderivC = -s u^{-s-1}); together with laplace_one (the 1/z      *)
(*  term) it assembles the Newman identity g(z)=Phi(z+1)/(z+1)-1/z.        *)
(* ================================================================= *)
