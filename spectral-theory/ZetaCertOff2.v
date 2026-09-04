(* ================================================================= *)
(*  ZetaCertOff2.v  --  the first certified value of zeta OFF the      *)
(*  critical line in this development.                                 *)
(*                                                                    *)
(*      0.68 <= Re zeta(3/2 + 2i) <= 0.83                              *)
(*     -0.41 <= Im zeta(3/2 + 2i) <= -0.26                             *)
(*                                                                    *)
(*  Every previous certified zeta value in the repository is at        *)
(*  sigma = 1/2 (ZetaEnclose.Izeta2 takes only an ordinate), because   *)
(*  the whole sign-certificate programme lives on the critical line.   *)
(*  The counting contour of the RH programme does not.                 *)
(*                                                                    *)
(*  Certificates live one per file, and the computation is inlined.    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith Bool.
Require Import ComplexField Cmodulus CZeta CZetaTerm FirstZeroBridge
        IntervalArith IntervalGint ZetaEM
        ZetaLineS ZetaEncloseS ZetaSBounds.
Open Scope R_scope.

Lemma chkOff2 :
  (match IzetaS 80 28 60 40 60 8 5 8 (3 # 2) 2 12 (7 # 100) with
   | Some (zr, zi) =>
       andb (andb (Qle_bool (68 # 100) (ilo zr)) (Qle_bool (ihi zr) (83 # 100)))
            (andb (Qle_bool (-41 # 100) (ilo zi))
                  (Qle_bool (ihi zi) (-26 # 100)))
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta_off_line_3half_2 :
  forall (H0 : 0 < Re (lineC (Q2R (3 # 2)) (Q2R 2)))
         (H1 : Cminus C1 (lineC (Q2R (3 # 2)) (Q2R 2)) <> C0),
  68 / 100 <= Re (zetaC (lineC (Q2R (3 # 2)) (Q2R 2)) H0 H1) <= 83 / 100
  /\ - (41 / 100) <= Im (zetaC (lineC (Q2R (3 # 2)) (Q2R 2)) H0 H1)
                  <= - (26 / 100).
Proof.
  intros H0 H1.
  assert (Esq : Q2R (3 # 2) = 3 / 2) by (unfold Q2R; simpl; lra).
  assert (Etq : Q2R 2 = 2) by (unfold Q2R; simpl; lra).
  assert (HI13 : INR (S 12) = 13)
    by (rewrite (INR_lit (S 12) 13%Z) by (vm_compute; reflexivity);
        simpl; lra).
  assert (HD : 0 < Dts (Q2R (3 # 2)) (Q2R 2))
    by (rewrite Esq, Etq; unfold Dts; nra).
  assert (HB : Kh (lineC (Q2R (3 # 2)) (Q2R 2))
               * Rpower (INR (S 12)) (- Re (lineC (Q2R (3 # 2)) (Q2R 2)))
               / INR (S 12) <= Q2R (7 # 100)).
  { rewrite Re_lineC, Esq, Etq, HI13.
    assert (Ht := tail_le_S (3 / 2) 2 12 (1 / 3) ltac:(lra) ltac:(lra)
                    ltac:(lra) ltac:(rewrite HI13; lra)).
    rewrite HI13 in Ht.
    assert (EB : Q2R (7 # 100) = 7 / 100) by (unfold Q2R; simpl; lra).
    rewrite EB; lra. }
  destruct (zetaS_bounds 80 28 60 40 60 8 5 8 (3 # 2) 2 12 (7 # 100)
              (68 # 100) (83 # 100) (-41 # 100) (-26 # 100)
              H0 H1 HD HB chkOff2) as [Hr Hi].
  assert (E1 : Q2R (68 # 100) = 68 / 100) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (83 # 100) = 83 / 100) by (unfold Q2R; simpl; lra).
  assert (E3 : Q2R (-41 # 100) = - (41 / 100)) by (unfold Q2R; simpl; lra).
  assert (E4 : Q2R (-26 # 100) = - (26 / 100)) by (unfold Q2R; simpl; lra).
  rewrite E1, E2 in Hr. rewrite E3, E4 in Hi.
  exact (conj Hr Hi).
Qed.

Print Assumptions zeta_off_line_3half_2.

(* ================================================================= *)
(*  END ZetaCertOff2.v -- zeta certified off the critical line.        *)
(* ================================================================= *)
