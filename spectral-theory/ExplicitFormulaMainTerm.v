(* ================================================================= *)
(*  ExplicitFormulaMainTerm.v  —  Explicit formula, Stage A brick 1:     *)
(*  the residue of the Perron kernel at the pole  s = 1  (the MAIN TERM). *)
(*                                                                    *)
(*  The Riemann-von Mangoldt explicit formula is obtained by shifting     *)
(*  the truncated Perron contour (PerronPsi.perron_psi_integral) left     *)
(*  past the poles of  Phi(s) x^s / s,  Phi = -zeta'/zeta.  The pole at    *)
(*  s = 1 (from zeta's pole, Phi(s) = 1/(s-1) + holomorphic) contributes   *)
(*  the residue of  y^s/(s-1),  namely  y  -- the  x  main term.          *)
(*                                                                    *)
(*  Here we prove that contour residue directly:  the shifted kernel      *)
(*  K1 y s = y^s/(s-1)  integrated counterclockwise around the rectangle  *)
(*  [-Uu,c] x [-T,T]  (which contains s=1 since c>1) equals  2*pi*i*y.     *)
(*  Mechanism: the shift  w = s-1  is POINTWISE on the shared parameter    *)
(*  (seg_R u = seg_{R'} u + 1), so via Cpw_split + Cpw_RtoC the kernel     *)
(*  factors as  y * (y^w/w),  reducing to PerronKernel.perron_rect_residue *)
(*  (the s=0 residue = 2*pi*i) on the rectangle shifted left by 1.         *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CIntegral2 CPathIntegral CSegInt
        CLeibniz PerronKernel PerronPower.
Open Scope R_scope.

Definition K1 (y : R) (s : C) : C := Cmul (Cpw y s) (Cinv (Cminus s C1)).
Notation KER0 y := (fun z => Cmul (Cpw y z) (Cinv z)).

Lemma Cpw_C1_val : forall y, 0 < y -> Cpw y C1 = RtoC y.
Proof.
  intros y Hy. change C1 with (RtoC 1). rewrite Cpw_RtoC.
  rewrite Rpower_1 by exact Hy. reflexivity.
Qed.

Lemma seg_shift : forall (P Q : C) u,
  seg P Q u = Cadd (seg (Cminus P C1) (Cminus Q C1) u) C1.
Proof.
  intros P Q u. unfold seg. apply Ceq;
    unfold Cadd, Cmul, Cminus, RtoC, C1; cbn [Re Im]; ring.
Qed.

Lemma segp_shift : forall (P Q : C) u,
  seg' P Q u = seg' (Cminus P C1) (Cminus Q C1) u.
Proof.
  intros P Q u. unfold seg'. apply Ceq; unfold Cminus; cbn [Re Im]; ring.
Qed.

Lemma edge_shift : forall y (P Q P' Q' : C)
  (Hf : Ccont (fun u => Cmul (K1 y (seg P Q u)) (seg' P Q u)))
  (Hg : Ccont (fun u => Cmul (Cmul (Cpw y (seg P' Q' u)) (Cinv (seg P' Q' u)))
                             (seg' P' Q' u))),
  0 < y -> P' = Cminus P C1 -> Q' = Cminus Q C1 ->
  pathint (seg P Q) (seg' P Q) (K1 y) Hf 0 1
  = Cmul (RtoC y) (pathint (seg P' Q') (seg' P' Q') (KER0 y) Hg 0 1).
Proof.
  intros y P Q P' Q' Hf Hg Hy HP HQ. subst P' Q'. unfold pathint.
  set (gR := fun u => Cmul (Cmul (Cpw y (seg (Cminus P C1) (Cminus Q C1) u))
                                 (Cinv (seg (Cminus P C1) (Cminus Q C1) u)))
                           (seg' (Cminus P C1) (Cminus Q C1) u)).
  rewrite <- (Cintf_cmul_l (RtoC y) gR Hg (Ccont_scal (RtoC y) gR Hg) 0 1 Rle_0_1).
  apply Cintf_ext. intro u. unfold gR, K1.
  set (S' := seg (Cminus P C1) (Cminus Q C1) u).
  rewrite (seg_shift P Q u), (segp_shift P Q u). fold S'.
  replace (Cminus (Cadd S' C1) C1) with S'
    by (apply Ceq; unfold Cadd, Cminus, C1; cbn [Re Im]; ring).
  rewrite (Cpw_split y S' C1), (Cpw_C1_val y Hy).
  set (a := Cpw y S'). set (b := seg' (Cminus P C1) (Cminus Q C1) u).
  set (iS := Cinv S'). ring.
Qed.

(* the residue at the s=1 pole:  the shifted Perron kernel y^s/(s-1) integrated
   counterclockwise around the rectangle [-Uu,c] x [-T,T] (which contains s=1,
   since c>1) equals 2 pi i * y. *)
Theorem rect_residue_pole1 : forall (y c Uu T : R),
  0 < y -> 1 < c -> 0 < Uu -> 0 < T ->
  forall
    (Hf1 : Ccont (fun u => Cmul (K1 y (seg (mkC c (- T)) (mkC c T) u))
                                (seg' (mkC c (- T)) (mkC c T) u)))
    (Hf2 : Ccont (fun u => Cmul (K1 y (seg (mkC c T) (mkC (- Uu) T) u))
                                (seg' (mkC c T) (mkC (- Uu) T) u)))
    (Hf3 : Ccont (fun u => Cmul (K1 y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u))
                                (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    (Hf4 : Ccont (fun u => Cmul (K1 y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u))
                                (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u)))
    (Hg1 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (c - 1) (- T)) (mkC (c - 1) T) u))
                                      (Cinv (seg (mkC (c - 1) (- T)) (mkC (c - 1) T) u)))
                                (seg' (mkC (c - 1) (- T)) (mkC (c - 1) T) u)))
    (Hg2 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (c - 1) T) (mkC (- (Uu + 1)) T) u))
                                      (Cinv (seg (mkC (c - 1) T) (mkC (- (Uu + 1)) T) u)))
                                (seg' (mkC (c - 1) T) (mkC (- (Uu + 1)) T) u)))
    (Hg3 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) u))
                                      (Cinv (seg (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) u)))
                                (seg' (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)) u)))
    (Hg4 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) u))
                                      (Cinv (seg (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) u)))
                                (seg' (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)) u))),
  Cadd (pathint (seg (mkC c (- T)) (mkC c T)) (seg' (mkC c (- T)) (mkC c T)) (K1 y) Hf1 0 1)
  (Cadd (pathint (seg (mkC c T) (mkC (- Uu) T)) (seg' (mkC c T) (mkC (- Uu) T)) (K1 y) Hf2 0 1)
  (Cadd (pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) (seg' (mkC (- Uu) T) (mkC (- Uu) (- T))) (K1 y) Hf3 0 1)
        (pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) (seg' (mkC (- Uu) (- T)) (mkC c (- T))) (K1 y) Hf4 0 1)))
  = mkC 0 (2 * PI * y).
Proof.
  intros y c Uu T Hy Hc HU HT Hf1 Hf2 Hf3 Hf4 Hg1 Hg2 Hg3 Hg4.
  assert (E : forall a b : R, mkC (a - 1) b = Cminus (mkC a b) C1)
    by (intros a b; apply Ceq; unfold Cminus, C1; cbn [Re Im]; ring).
  assert (Eo : forall b : R, mkC (- (Uu + 1)) b = Cminus (mkC (- Uu) b) C1)
    by (intro b; apply Ceq; unfold Cminus, C1; cbn [Re Im]; ring).
  rewrite (edge_shift y (mkC c (- T)) (mkC c T) _ _ Hf1 Hg1 Hy (E c (- T)) (E c T)).
  rewrite (edge_shift y (mkC c T) (mkC (- Uu) T) _ _ Hf2 Hg2 Hy (E c T) (Eo T)).
  rewrite (edge_shift y (mkC (- Uu) T) (mkC (- Uu) (- T)) _ _ Hf3 Hg3 Hy (Eo T) (Eo (- T))).
  rewrite (edge_shift y (mkC (- Uu) (- T)) (mkC c (- T)) _ _ Hf4 Hg4 Hy (Eo (- T)) (E c (- T))).
  pose proof (perron_rect_residue y (c - 1) (Uu + 1) T Hy ltac:(lra) ltac:(lra) HT
                Hg1 Hg2 Hg3 Hg4) as Hperr.
  set (A := pathint (seg (mkC (c - 1) (- T)) (mkC (c - 1) T))
              (seg' (mkC (c - 1) (- T)) (mkC (c - 1) T)) (KER0 y) Hg1 0 1) in *.
  set (B := pathint (seg (mkC (c - 1) T) (mkC (- (Uu + 1)) T))
              (seg' (mkC (c - 1) T) (mkC (- (Uu + 1)) T)) (KER0 y) Hg2 0 1) in *.
  set (Cc := pathint (seg (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T)))
              (seg' (mkC (- (Uu + 1)) T) (mkC (- (Uu + 1)) (- T))) (KER0 y) Hg3 0 1) in *.
  set (D := pathint (seg (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T)))
              (seg' (mkC (- (Uu + 1)) (- T)) (mkC (c - 1) (- T))) (KER0 y) Hg4 0 1) in *.
  replace (Cadd (Cmul (RtoC y) A) (Cadd (Cmul (RtoC y) B)
                (Cadd (Cmul (RtoC y) Cc) (Cmul (RtoC y) D))))
    with (Cmul (RtoC y) (Cadd A (Cadd B (Cadd Cc D)))) by ring.
  rewrite Hperr. apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring.
Qed.

Print Assumptions rect_residue_pole1.
