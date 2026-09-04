(* ================================================================= *)
(*  ZetaCertHalf2.v  --  the regression certificate.                   *)
(*                                                                    *)
(*  At sq = 1/2 the sigma-general evaluator must reproduce the         *)
(*  committed critical-line one.  It does so BIT-IDENTICALLY:          *)
(*                                                                    *)
(*    IzetaS ... (1#2) 2 12 (4#100) = Izeta2 ... 2 12 (4#100)          *)
(*                                                                    *)
(*  which is the strongest available check that all six sigma sites    *)
(*  were generalised correctly -- in particular the sign trap, where   *)
(*  the head term carries (sg-1)/D and the G term (1-sg)/D, equal and  *)
(*  opposite at sg = 1/2.  A sign flip there would shift Im by 2 vq    *)
(*  and this equality would fail.                                     *)
(*                                                                    *)
(*  Certificates live one per file: the repo records that bundling     *)
(*  five cost 92 minutes serial where separate files ran 19 in         *)
(*  parallel.  The computation is INLINED, never routed through a      *)
(*  Definition, which would make Qed re-run it.                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith Bool.
Require Import ComplexField Cmodulus CZeta CZetaTerm FirstZeroBridge
        IntervalArith IntervalGint ZetaEM ZetaEnclose
        ZetaLineS ZetaEncloseS ZetaSBounds.
Open Scope R_scope.

(* ---- the two evaluators agree exactly where they overlap ---- *)

Theorem IzetaS_matches_Izeta2 :
  IzetaS 80 28 60 40 60 8 5 8 (1#2) 2 12 (4#100)
  = Izeta2 80 28 60 40 60 8 5 8 2 12 (4#100).
Proof. vm_compute. reflexivity. Qed.

(* ---- and the enclosure itself ---- *)

Lemma chkH2 :
  (match IzetaS 80 28 60 40 60 8 5 8 (1#2) 2 12 (4#100) with
   | Some (zr, zi) =>
       andb (andb (Qle_bool (40 # 100) (ilo zr)) (Qle_bool (ihi zr) (49 # 100)))
            (andb (Qle_bool (-36 # 100) (ilo zi))
                  (Qle_bool (ihi zi) (-27 # 100)))
   | None => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zeta_half_2 :
  forall (H0 : 0 < Re (lineC (Q2R (1 # 2)) (Q2R 2)))
         (H1 : Cminus C1 (lineC (Q2R (1 # 2)) (Q2R 2)) <> C0),
  40 / 100 <= Re (zetaC (lineC (Q2R (1 # 2)) (Q2R 2)) H0 H1) <= 49 / 100
  /\ - (36 / 100) <= Im (zetaC (lineC (Q2R (1 # 2)) (Q2R 2)) H0 H1)
                  <= - (27 / 100).
Proof.
  intros H0 H1.
  assert (Esq : Q2R (1 # 2) = / 2) by (unfold Q2R; simpl; lra).
  assert (Etq : Q2R 2 = 2) by (unfold Q2R; simpl; lra).
  assert (HI13 : INR (S 12) = 13)
    by (rewrite (INR_lit (S 12) 13%Z) by (vm_compute; reflexivity);
        simpl; lra).
  assert (HD : 0 < Dts (Q2R (1 # 2)) (Q2R 2))
    by (rewrite Esq, Etq; unfold Dts; nra).
  assert (HB : Kh (lineC (Q2R (1 # 2)) (Q2R 2))
               * Rpower (INR (S 12)) (- Re (lineC (Q2R (1 # 2)) (Q2R 2)))
               / INR (S 12) <= Q2R (4 # 100)).
  { rewrite Re_lineC, Esq, Etq, HI13.
    assert (Ht := tail_le_S (/ 2) 2 12 (1 / 3) ltac:(lra) ltac:(lra)
                    ltac:(lra) ltac:(rewrite HI13; lra)).
    rewrite HI13 in Ht.
    assert (EB : Q2R (4 # 100) = 4 / 100) by (unfold Q2R; simpl; lra).
    rewrite EB; lra. }
  destruct (zetaS_bounds 80 28 60 40 60 8 5 8 (1 # 2) 2 12 (4 # 100)
              (40 # 100) (49 # 100) (-36 # 100) (-27 # 100)
              H0 H1 HD HB chkH2) as [Hr Hi].
  assert (E1 : Q2R (40 # 100) = 40 / 100) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (49 # 100) = 49 / 100) by (unfold Q2R; simpl; lra).
  assert (E3 : Q2R (-36 # 100) = - (36 / 100)) by (unfold Q2R; simpl; lra).
  assert (E4 : Q2R (-27 # 100) = - (27 / 100)) by (unfold Q2R; simpl; lra).
  rewrite E1, E2 in Hr. rewrite E3, E4 in Hi.
  exact (conj Hr Hi).
Qed.

Print Assumptions zeta_half_2.

(* ================================================================= *)
(*  END ZetaCertHalf2.v                                               *)
(* ================================================================= *)
