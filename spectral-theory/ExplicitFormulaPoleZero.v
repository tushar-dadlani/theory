(* ================================================================= *)
(*  ExplicitFormulaPoleZero.v  —  Explicit formula, Stage A brick 3:     *)
(*  the residue at a general complex pole (the per-ZERO term  x^rho).     *)
(*                                                                    *)
(*  In the explicit formula, Phi = -zeta'/zeta has a simple pole at each   *)
(*  nontrivial zero rho, so the kernel Phi(s) x^s/s contributes the        *)
(*  residue of  x^s/(s-rho)  at s=rho, whose numerator is  x^rho.  Here we *)
(*  prove that residue for an ARBITRARY complex pole a:                    *)
(*                                                                    *)
(*    rect_residue_poleC :  KpoleC y a s = y^s/(s-a)  integrated ccw       *)
(*    around the a-centred rectangle  a + [-Uu,c] x [-T,T]  (which         *)
(*    contains a, since 0 is interior to [-Uu,c] x [-T,T])  equals         *)
(*    2*pi*i * y^a   ( = Cmul (mkC 0 (2*pi)) (Cpw y a) ).                   *)
(*                                                                    *)
(*  This generalises ExplicitFormulaMainTerm.rect_residue_pole1 (the a=1   *)
(*  case) to a genuinely COMPLEX pole location.  Mechanism (edge_shiftC):  *)
(*  the shift w = s - a is pointwise on the shared segment parameter       *)
(*  (seg_R u = seg_{R'} u + a), and Cpw_split factors the kernel as        *)
(*  y^a * (y^w/w), reducing each edge to PerronKernel.perron_rect_residue  *)
(*  on the a-centred rectangle shifted back to the origin.                 *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CIntegral2 CPathIntegral CSegInt
        CLeibniz PerronKernel PerronPower.
Open Scope R_scope.

(* the Perron kernel with a general complex pole a:  y^s / (s - a) *)
Definition KpoleC (y : R) (a s : C) : C := Cmul (Cpw y s) (Cinv (Cminus s a)).

Lemma seg_shiftC : forall (a P Q : C) u,
  seg P Q u = Cadd (seg (Cminus P a) (Cminus Q a) u) a.
Proof.
  intros a P Q u. unfold seg. apply Ceq;
    unfold Cadd, Cmul, Cminus, RtoC; cbn [Re Im]; ring.
Qed.
Lemma segp_shiftC : forall (a P Q : C) u,
  seg' P Q u = seg' (Cminus P a) (Cminus Q a) u.
Proof.
  intros a P Q u. unfold seg'. apply Ceq; unfold Cminus; cbn [Re Im]; ring.
Qed.
Lemma shift_back : forall a P0 : C, P0 = Cminus (Cadd a P0) a.
Proof. intros a P0. apply Ceq; unfold Cadd, Cminus; cbn [Re Im]; ring. Qed.

(* one edge:  int of y^s/(s-a)  =  y^a * (int of y^w/w  over the edge shifted by -a) *)
Lemma edge_shiftC : forall y (a P Q P' Q' : C)
  (Hf : Ccont (fun u => Cmul (KpoleC y a (seg P Q u)) (seg' P Q u)))
  (Hg : Ccont (fun u => Cmul (Cmul (Cpw y (seg P' Q' u)) (Cinv (seg P' Q' u)))
                             (seg' P' Q' u))),
  0 < y -> P' = Cminus P a -> Q' = Cminus Q a ->
  pathint (seg P Q) (seg' P Q) (KpoleC y a) Hf 0 1
  = Cmul (Cpw y a)
      (pathint (seg P' Q') (seg' P' Q') (fun z => Cmul (Cpw y z) (Cinv z)) Hg 0 1).
Proof.
  intros y a P Q P' Q' Hf Hg Hy HP HQ. subst P' Q'. unfold pathint.
  set (gR := fun u => Cmul (Cmul (Cpw y (seg (Cminus P a) (Cminus Q a) u))
                                 (Cinv (seg (Cminus P a) (Cminus Q a) u)))
                           (seg' (Cminus P a) (Cminus Q a) u)).
  rewrite <- (Cintf_cmul_l (Cpw y a) gR Hg (Ccont_scal (Cpw y a) gR Hg) 0 1 Rle_0_1).
  apply Cintf_ext. intro u. unfold gR, KpoleC.
  set (S' := seg (Cminus P a) (Cminus Q a) u).
  rewrite (seg_shiftC a P Q u), (segp_shiftC a P Q u). fold S'.
  replace (Cminus (Cadd S' a) a) with S'
    by (apply Ceq; unfold Cadd, Cminus; cbn [Re Im]; ring).
  rewrite (Cpw_split y S' a).
  set (p := Cpw y S'). set (q := Cpw y a).
  set (b := seg' (Cminus P a) (Cminus Q a) u). set (iS := Cinv S'). ring.
Qed.

(* the residue of  y^s/(s-a)  at the pole  s = a  (any complex a):  the kernel
   integrated ccw around the a-centred rectangle  a + [-Uu,c] x [-T,T]  equals
   2*pi*i * y^a.  (Generalises rect_residue_pole1, the a = 1 case.) *)
Theorem rect_residue_poleC : forall (y : R) (a : C) (c Uu T : R),
  0 < y -> 0 < c -> 0 < Uu -> 0 < T ->
  forall
    (Hf1 : Ccont (fun u => Cmul (KpoleC y a (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) u))
                                (seg' (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) u)))
    (Hf2 : Ccont (fun u => Cmul (KpoleC y a (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) u))
                                (seg' (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) u)))
    (Hf3 : Ccont (fun u => Cmul (KpoleC y a (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) u))
                                (seg' (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) u)))
    (Hf4 : Ccont (fun u => Cmul (KpoleC y a (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) u))
                                (seg' (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) u)))
    (Hg1 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c (- T)) (mkC c T) u)) (Cinv (seg (mkC c (- T)) (mkC c T) u)))
                                (seg' (mkC c (- T)) (mkC c T) u)))
    (Hg2 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC c T) (mkC (- Uu) T) u)) (Cinv (seg (mkC c T) (mkC (- Uu) T) u)))
                                (seg' (mkC c T) (mkC (- Uu) T) u)))
    (Hg3 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u)) (Cinv (seg (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
                                (seg' (mkC (- Uu) T) (mkC (- Uu) (- T)) u)))
    (Hg4 : Ccont (fun u => Cmul (Cmul (Cpw y (seg (mkC (- Uu) (- T)) (mkC c (- T)) u)) (Cinv (seg (mkC (- Uu) (- T)) (mkC c (- T)) u)))
                                (seg' (mkC (- Uu) (- T)) (mkC c (- T)) u))),
  Cadd (pathint (seg (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) (seg' (Cadd a (mkC c (- T))) (Cadd a (mkC c T))) (KpoleC y a) Hf1 0 1)
  (Cadd (pathint (seg (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) (seg' (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T))) (KpoleC y a) Hf2 0 1)
  (Cadd (pathint (seg (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) (seg' (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T)))) (KpoleC y a) Hf3 0 1)
        (pathint (seg (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) (seg' (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T)))) (KpoleC y a) Hf4 0 1)))
  = Cmul (mkC 0 (2 * PI)) (Cpw y a).
Proof.
  intros y a c Uu T Hy Hc HU HT Hf1 Hf2 Hf3 Hf4 Hg1 Hg2 Hg3 Hg4.
  rewrite (edge_shiftC y a (Cadd a (mkC c (- T))) (Cadd a (mkC c T)) _ _ Hf1 Hg1 Hy
             (shift_back a (mkC c (- T))) (shift_back a (mkC c T))).
  rewrite (edge_shiftC y a (Cadd a (mkC c T)) (Cadd a (mkC (- Uu) T)) _ _ Hf2 Hg2 Hy
             (shift_back a (mkC c T)) (shift_back a (mkC (- Uu) T))).
  rewrite (edge_shiftC y a (Cadd a (mkC (- Uu) T)) (Cadd a (mkC (- Uu) (- T))) _ _ Hf3 Hg3 Hy
             (shift_back a (mkC (- Uu) T)) (shift_back a (mkC (- Uu) (- T)))).
  rewrite (edge_shiftC y a (Cadd a (mkC (- Uu) (- T))) (Cadd a (mkC c (- T))) _ _ Hf4 Hg4 Hy
             (shift_back a (mkC (- Uu) (- T))) (shift_back a (mkC c (- T)))).
  pose proof (perron_rect_residue y c Uu T Hy Hc HU HT Hg1 Hg2 Hg3 Hg4) as Hperr.
  set (A := pathint (seg (mkC c (- T)) (mkC c T)) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hg1 0 1) in *.
  set (B := pathint (seg (mkC c T) (mkC (- Uu) T)) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hg2 0 1) in *.
  set (Cc := pathint (seg (mkC (- Uu) T) (mkC (- Uu) (- T))) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hg3 0 1) in *.
  set (D := pathint (seg (mkC (- Uu) (- T)) (mkC c (- T))) _ (fun z => Cmul (Cpw y z) (Cinv z)) Hg4 0 1) in *.
  replace (Cadd (Cmul (Cpw y a) A) (Cadd (Cmul (Cpw y a) B)
                (Cadd (Cmul (Cpw y a) Cc) (Cmul (Cpw y a) D))))
    with (Cmul (Cpw y a) (Cadd A (Cadd B (Cadd Cc D)))) by ring.
  rewrite Hperr. ring.
Qed.

Print Assumptions rect_residue_poleC.
