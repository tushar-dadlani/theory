(* ================================================================= *)
(*  CheapSign.v  --  a reusable sign certificate for xir.             *)
(*                                                                    *)
(*  ZeroCounting.alternation_zeros already turns n+1 alternating sign  *)
(*  values into a zero in each of the n gaps, so generalising to many  *)
(*  zeros needs no new counting theory -- only cheap, REUSABLE sign    *)
(*  certificates.  ThirdZeroCheap was bespoke to t = 26; here the      *)
(*  whole pipeline (theta by ThetaEnclose, zeta by ZetaEnclose, the    *)
(*  combination by ZSign) is packaged so that each new sample point    *)
(*  costs one tail-bound discharge and one vm_compute.                *)
(*                                                                    *)
(*  As always the computation is INLINED in the boolean hypothesis;    *)
(*  routing it through a Definition makes Qed re-run the whole thing.  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith.
Require Import ComplexField Cmodulus CZeta ZetaFn CoherenceSingularity
        IntervalArith IntervalAtan XirSignZ GammaArg ThetaEnclose
        ZetaEM ZetaEnclose ZSign.
Open Scope R_scope.

Theorem xir_neg_cheap : forall p m pl pr pc mc nc K tq M Bq
    prt Mt Mat nt thr,
  0 < Q2R tq -> 0 < Q2R thr -> (1 <= nt)%nat ->
  Kh (crit (Q2R tq))
    * Rpower (INR (S M)) (- Re (crit (Q2R tq))) / INR (S M) <= Q2R Bq ->
  (match Izeta2 p m pl pr pc mc nc K tq M Bq with
   | Some (zr, zi) =>
       match IZ pc mc nc (Itheta prt Mt Mat tq nt) zr zi with
       | Some i => Qle_bool thr (ilo i)
       | None => false
       end
   | None => false
   end) = true ->
  xir (Q2R tq) < 0.
Proof.
  intros p m pl pr pc mc nc K tq M Bq prt Mt Mat nt thr Ht Hthr Hnt HB Hc.
  assert (H0 : 0 < Re (crit (Q2R tq))) by (unfold crit; cbn [Re]; lra).
  assert (H1 : Cminus C1 (crit (Q2R tq)) <> C0) by apply crit_ne1.
  destruct (Izeta2 p m pl pr pc mc nc K tq M Bq) as [[zr zi] |] eqn:HZ;
    [ | discriminate ].
  destruct (IZ pc mc nc (Itheta prt Mt Mat tq nt) zr zi) as [i |] eqn:HI;
    [ | discriminate ].
  apply Qle_R' in Hc.
  destruct (Izeta2_sound p m pl pr pc mc nc K tq M Bq zr zi H0 H1 HB HZ)
    as [Zr Zi].
  apply (xir_neg_of_IZ pc mc nc (Itheta prt Mt Mat tq nt) zr zi i (Q2R tq)).
  - lra.
  - apply Itheta_sound; assumption.
  - rewrite (zF_eq (crit (Q2R tq)) H0 H1). exact Zr.
  - rewrite (zF_eq (crit (Q2R tq)) H0 H1). exact Zi.
  - exact HI.
  - lra.
Qed.

Theorem xir_pos_cheap : forall p m pl pr pc mc nc K tq M Bq
    prt Mt Mat nt thr,
  0 < Q2R tq -> 0 < Q2R thr -> (1 <= nt)%nat ->
  Kh (crit (Q2R tq))
    * Rpower (INR (S M)) (- Re (crit (Q2R tq))) / INR (S M) <= Q2R Bq ->
  (match Izeta2 p m pl pr pc mc nc K tq M Bq with
   | Some (zr, zi) =>
       match IZ pc mc nc (Itheta prt Mt Mat tq nt) zr zi with
       | Some i => Qle_bool (ihi i) (Qopp thr)
       | None => false
       end
   | None => false
   end) = true ->
  0 < xir (Q2R tq).
Proof.
  intros p m pl pr pc mc nc K tq M Bq prt Mt Mat nt thr Ht Hthr Hnt HB Hc.
  assert (H0 : 0 < Re (crit (Q2R tq))) by (unfold crit; cbn [Re]; lra).
  assert (H1 : Cminus C1 (crit (Q2R tq)) <> C0) by apply crit_ne1.
  destruct (Izeta2 p m pl pr pc mc nc K tq M Bq) as [[zr zi] |] eqn:HZ;
    [ | discriminate ].
  destruct (IZ pc mc nc (Itheta prt Mt Mat tq nt) zr zi) as [i |] eqn:HI;
    [ | discriminate ].
  apply Qle_R' in Hc. rewrite Q2R_opp in Hc.
  destruct (Izeta2_sound p m pl pr pc mc nc K tq M Bq zr zi H0 H1 HB HZ)
    as [Zr Zi].
  apply (xir_pos_of_IZ pc mc nc (Itheta prt Mt Mat tq nt) zr zi i (Q2R tq)).
  - lra.
  - apply Itheta_sound; assumption.
  - rewrite (zF_eq (crit (Q2R tq)) H0 H1). exact Zr.
  - rewrite (zF_eq (crit (Q2R tq)) H0 H1). exact Zi.
  - exact HI.
  - lra.
Qed.
