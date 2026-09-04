(* ================================================================= *)
(*  ZetaEncloseS.v  --  a certified interval for zeta on ANY vertical  *)
(*  line Re s = sq, sq rational and positive.                          *)
(*                                                                    *)
(*  ZetaEnclose.Izeta2 does this at sq = 1/2 only.  The RH counting    *)
(*  contour needs zeta off the critical line, so the pipeline is       *)
(*  mirrored with sq as a parameter.  Everything sigma-free is         *)
(*  IMPORTED rather than duplicated: mkterm, Lnext, Icos_itvc,         *)
(*  Isin_itvc, Q2R_phalf, inv_sqrt_le, and the whole interval library. *)
(*  ZetaEnclose.v itself is untouched, so the existing (expensive)     *)
(*  certificate chain is not rebuilt.                                  *)
(*                                                                    *)
(*  THE TAIL BOUND.  ZetaEnclose.tail_le discharges                     *)
(*  Rpower (M+1) (-1/2) by Rpower_sqrt plus a rational certificate     *)
(*  1 <= r^2 (M+1) -- no square root is ever computed.  Rpower_sqrt    *)
(*  exists only at the exponent 1/2.  Rather than build a general      *)
(*  r^b (M+1)^a >= 1 lemma, note that for sg >= 1/2                    *)
(*      (M+1)^{-sg} <= (M+1)^{-1/2}     (Rle_Rpower)                   *)
(*  so the SAME rational certificate serves, slightly loosely.  And    *)
(*  sg >= 1/2 is all a contour symmetric under s |-> 1-s ever needs,   *)
(*  since XiC_symmetric and XiC_conj make the left and bottom edges    *)
(*  reflections of the right and top.                                  *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith Bool.
Require Import ComplexField Cmodulus CSeries CZetaTerm CZeta CoherenceSingularity
        IntervalArith IntervalArithFun IntervalCos IntervalLn IntervalGint
        IntervalAtan IntervalTrig IntervalLnSeries LnSeries CertifiedPi
        ZetaCrit ZetaTrap ZetaEM ZetaEnclose ZetaLineS.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  The head term 1/(s-1), as exact rationals.                         *)
(* ----------------------------------------------------------------- *)

Definition Dq (sq tq : Q) : Q :=
  Qplus (Qmult (Qminus 1 sq) (Qminus 1 sq)) (Qmult tq tq).

Definition uqs (sq tq : Q) : Q := Qdiv (Qminus 1 sq) (Dq sq tq).
Definition vqs (sq tq : Q) : Q := Qdiv tq (Dq sq tq).

Lemma Q2R_Dq : forall sq tq,
  Q2R (Dq sq tq) = Dts (Q2R sq) (Q2R tq).
Proof.
  intros sq tq; unfold Dq, Dts.
  rewrite Q2R_plus, !Q2R_mult, Q2R_minus.
  replace (Q2R 1) with 1 by (unfold Q2R; simpl; lra). ring.
Qed.

Lemma Dq_ne0 : forall sq tq, 0 < Dts (Q2R sq) (Q2R tq) ->
  ~ (Dq sq tq == 0)%Q.
Proof.
  intros sq tq HD; apply Qne0_of_R; rewrite Q2R_Dq; apply Rgt_not_eq; lra.
Qed.

Lemma Q2R_uqs : forall sq tq, 0 < Dts (Q2R sq) (Q2R tq) ->
  Q2R (uqs sq tq) = (1 - Q2R sq) / Dts (Q2R sq) (Q2R tq).
Proof.
  intros sq tq HD; unfold uqs.
  rewrite Q2R_div by (apply Dq_ne0; exact HD).
  rewrite Q2R_Dq, Q2R_minus.
  replace (Q2R 1) with 1 by (unfold Q2R; simpl; lra). reflexivity.
Qed.

Lemma Q2R_vqs : forall sq tq, 0 < Dts (Q2R sq) (Q2R tq) ->
  Q2R (vqs sq tq) = Q2R tq / Dts (Q2R sq) (Q2R tq).
Proof.
  intros sq tq HD; unfold vqs.
  rewrite Q2R_div by (apply Dq_ne0; exact HD).
  rewrite Q2R_Dq; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  The four components at one integer, at general sq.                 *)
(*  Only two constants change from Iquad': -1/2 becomes -sq, and       *)
(*  1/2 becomes 1-sq.                                                  *)
(* ----------------------------------------------------------------- *)

Definition IquadS (p m pr pc mc nc : nat) (sq tq : Q) (L : Itv)
  : option (Itv * Itv * Itv * Itv) :=
  let AR := Iround pr (Imul (Iconst tq) L) in
  match Iexp_itvc p m (Iround pr (Imul (Iconst (Qopp sq)) L)),
        Iexp_itvc p m (Iround pr (Imul (Iconst (Qminus 1 sq)) L)),
        Icos_itvc pc mc nc AR, Isin_itvc pc mc nc AR with
  | Some P, Some Qv, Some A, Some Sv =>
      Some (Imul P A,
            Ineg (Imul P Sv),
            Imul Qv (Iadd (Imul A (Iconst (uqs sq tq)))
                          (Imul Sv (Iconst (vqs sq tq)))),
            Imul Qv (Isub (Imul A (Iconst (vqs sq tq)))
                          (Imul Sv (Iconst (uqs sq tq)))))
  | _, _, _, _ => None
  end.

Definition QuadOKS (sq tq : Q) (x : R) (q : Itv * Itv * Itv * Itv) : Prop :=
  let '(rg, ig, rG, iG) := q in
  Icontains rg (Re (gC (lineC (Q2R sq) (Q2R tq)) x))
  /\ Icontains ig (Im (gC (lineC (Q2R sq) (Q2R tq)) x))
  /\ Icontains rG (Re (GC (lineC (Q2R sq) (Q2R tq)) x))
  /\ Icontains iG (Im (GC (lineC (Q2R sq) (Q2R tq)) x)).

Lemma IquadS_sound : forall p m pr pc mc nc sq tq L x q,
  0 < Dts (Q2R sq) (Q2R tq) ->
  Icontains L (ln x) ->
  IquadS p m pr pc mc nc sq tq L = Some q -> QuadOKS sq tq x q.
Proof.
  intros p m pr pc mc nc sq tq L x q HD HL H. unfold IquadS in H.
  set (AR := Iround pr (Imul (Iconst tq) L)) in *.
  assert (HAR : Icontains AR (Q2R tq * ln x))
    by (unfold AR; apply Iround_sound, Imul_sound;
        [ apply Iconst_sound | exact HL ]).
  destruct (Iexp_itvc p m (Iround pr (Imul (Iconst (Qopp sq)) L))) eqn:HP;
    [ | discriminate ].
  destruct (Iexp_itvc p m (Iround pr (Imul (Iconst (Qminus 1 sq)) L))) eqn:HQ;
    [ | discriminate ].
  destruct (Icos_itvc pc mc nc AR) eqn:HA; [ | discriminate ].
  destruct (Isin_itvc pc mc nc AR) eqn:HS; [ | discriminate ].
  injection H as <-.
  assert (HPc : Icontains i (exp (- Q2R sq * ln x))).
  { eapply Iexp_itvc_sound; [ exact HP | ].
    replace (- Q2R sq * ln x) with (Q2R (Qopp sq) * ln x)
      by (rewrite Q2R_opp; ring).
    apply Iround_sound, Imul_sound; [ apply Iconst_sound | exact HL ]. }
  assert (HQc : Icontains i0 (exp ((1 - Q2R sq) * ln x))).
  { eapply Iexp_itvc_sound; [ exact HQ | ].
    replace ((1 - Q2R sq) * ln x) with (Q2R (Qminus 1 sq) * ln x)
      by (rewrite Q2R_minus;
          replace (Q2R 1) with 1 by (unfold Q2R; simpl; lra); ring).
    apply Iround_sound, Imul_sound; [ apply Iconst_sound | exact HL ]. }
  assert (HAc : Icontains i1 (cos (Q2R tq * ln x)))
    by (apply (Icos_itvc_sound pc mc nc AR); assumption).
  assert (HSc : Icontains i2 (sin (Q2R tq * ln x)))
    by (apply (Isin_itvc_sound pc mc nc AR); assumption).
  unfold QuadOKS. refine (conj _ (conj _ (conj _ _))).
  - rewrite Re_gC_line. apply Imul_sound; assumption.
  - rewrite Im_gC_line. apply Ineg_sound. apply Imul_sound; assumption.
  - rewrite Re_GC_line by exact HD. apply Imul_sound; [ exact HQc | ].
    apply Iadd_sound; apply Imul_sound; try assumption;
      [ rewrite <- (Q2R_uqs sq tq HD); apply Iconst_sound
      | rewrite <- (Q2R_vqs sq tq HD); apply Iconst_sound ].
  - rewrite Im_GC_line by exact HD. apply Imul_sound; [ exact HQc | ].
    apply Isub_sound; apply Imul_sound; try assumption;
      [ rewrite <- (Q2R_vqs sq tq HD); apply Iconst_sound
      | rewrite <- (Q2R_uqs sq tq HD); apply Iconst_sound ].
Qed.

(* mkterm is sigma-free; only its soundness statement mentions the line *)
Lemma mktermS_sound : forall sq tq n qa qb tr ti,
  QuadOKS sq tq (INR (S n)) qa -> QuadOKS sq tq (INR (S (S n))) qb ->
  mkterm qa qb = (tr, ti) ->
  Icontains tr (Re (htermC (lineC (Q2R sq) (Q2R tq)) n))
  /\ Icontains ti (Im (htermC (lineC (Q2R sq) (Q2R tq)) n)).
Proof.
  intros sq tq n [[[ra ia] Ra] Ia] [[[rb ib] Rb] Ib] tr ti
    [A1 [A2 [A3 A4]]] [B1 [B2 [B3 B4]]] H.
  cbn [mkterm] in H. injection H as <- <-.
  split.
  - rewrite Re_htermC. apply Isub_sound.
    + rewrite <- Q2R_phalf. apply Imul_sound;
        [ apply Iconst_sound | apply Iadd_sound; assumption ].
    + apply Isub_sound; assumption.
  - rewrite Im_htermC. apply Isub_sound.
    + rewrite <- Q2R_phalf. apply Imul_sound;
        [ apply Iconst_sound | apply Iadd_sound; assumption ].
    + apply Isub_sound; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  The linear-cost sum: ISum2 with sq threaded through.               *)
(* ----------------------------------------------------------------- *)

Fixpoint ISum2S (p m pl pr pc mc nc K : nat) (sq tq : Q) (M : nat)
  : option (Itv * Itv * Itv * (Itv * Itv * Itv * Itv)) :=
  match M with
  | O =>
      match IquadS p m pr pc mc nc sq tq (Iconst 0),
            IquadS p m pr pc mc nc sq tq (Lnext pl K 1 (Iconst 0)) with
      | Some q1, Some q2 =>
          match mkterm q1 q2 with
          | (tr, ti) => Some (tr, ti, Lnext pl K 1 (Iconst 0), q2)
          end
      | _, _ => None
      end
  | S k =>
      match ISum2S p m pl pr pc mc nc K sq tq k with
      | Some (r, i, Lb, qb) =>
          match IquadS p m pr pc mc nc sq tq (Lnext pl K (S (S k)) Lb) with
          | Some qc =>
              match mkterm qb qc with
              | (tr, ti) =>
                  Some (Iround pr (Iadd r tr), Iround pr (Iadd i ti),
                        Lnext pl K (S (S k)) Lb, qc)
              end
          | None => None
          end
      | None => None
      end
  end.

Lemma ISum2S_sound : forall p m pl pr pc mc nc K sq tq M r i Lb qb,
  0 < Dts (Q2R sq) (Q2R tq) ->
  ISum2S p m pl pr pc mc nc K sq tq M = Some (r, i, Lb, qb) ->
  Icontains r (Re (Cpsum (htermC (lineC (Q2R sq) (Q2R tq))) M))
  /\ Icontains i (Im (Cpsum (htermC (lineC (Q2R sq) (Q2R tq))) M))
  /\ Icontains Lb (ln (INR (S (S M))))
  /\ QuadOKS sq tq (INR (S (S M))) qb.
Proof.
  intros p m pl pr pc mc nc K sq tq M.
  induction M as [| M IH0]; intros r i Lb qb HD H.
  - cbn [ISum2S] in H.
    assert (HL1 : Icontains (Iconst 0) (ln (INR 1))).
    { replace (INR 1) with 1 by (simpl; ring). rewrite ln_1.
      replace 0 with (Q2R 0) by apply Q2R_zero. apply Iconst_sound. }
    assert (HL2 : Icontains (Lnext pl K 1 (Iconst 0)) (ln (INR 2)))
      by (apply (Lnext_sound pl K 1); [ lia | exact HL1 ]).
    destruct (IquadS p m pr pc mc nc sq tq (Iconst 0)) as [q1 |] eqn:Hq1;
      [ | discriminate ].
    destruct (IquadS p m pr pc mc nc sq tq (Lnext pl K 1 (Iconst 0)))
      as [q2 |] eqn:Hq2; [ | discriminate ].
    destruct (mkterm q1 q2) as [tr ti] eqn:Hm.
    injection H as <- <- <- <-.
    assert (Q1 : QuadOKS sq tq (INR 1) q1)
      by (apply (IquadS_sound p m pr pc mc nc sq tq (Iconst 0)); assumption).
    assert (Q2 : QuadOKS sq tq (INR 2) q2)
      by (apply (IquadS_sound p m pr pc mc nc sq tq
                   (Lnext pl K 1 (Iconst 0))); assumption).
    destruct (mktermS_sound sq tq 0 q1 q2 tr ti Q1 Q2 Hm) as [T1 T2].
    cbn [Cpsum]. exact (conj T1 (conj T2 (conj HL2 Q2))).
  - cbn [ISum2S] in H.
    destruct (ISum2S p m pl pr pc mc nc K sq tq M) as [[[[r0 i0] Lb0] qb0] |]
      eqn:Hs; [ | discriminate ].
    destruct (IH0 r0 i0 Lb0 qb0 HD eq_refl) as [S1 [S2 [S3 S4]]].
    destruct (IquadS p m pr pc mc nc sq tq (Lnext pl K (S (S M)) Lb0))
      as [qc |] eqn:Hqc; [ | discriminate ].
    destruct (mkterm qb0 qc) as [tr ti] eqn:Hm.
    injection H as <- <- <- <-.
    assert (HLc : Icontains (Lnext pl K (S (S M)) Lb0)
                    (ln (INR (S (S (S M))))))
      by (apply (Lnext_sound pl K (S (S M))); [ lia | exact S3 ]).
    assert (Qc : QuadOKS sq tq (INR (S (S (S M)))) qc)
      by (apply (IquadS_sound p m pr pc mc nc sq tq
                   (Lnext pl K (S (S M)) Lb0)); assumption).
    destruct (mktermS_sound sq tq (S M) qb0 qc tr ti S4 Qc Hm) as [T1 T2].
    cbn [Cpsum].
    refine (conj _ (conj _ (conj HLc Qc))).
    + rewrite Re_Cadd'. apply Iround_sound, Iadd_sound; assumption.
    + rewrite Im_Cadd'. apply Iround_sound, Iadd_sound; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  The enclosure.                                                     *)
(* ----------------------------------------------------------------- *)

Definition IzetaS (p m pl pr pc mc nc K : nat) (sq tq : Q) (M : nat) (Bq : Q)
  : option (Itv * Itv) :=
  match ISum2S p m pl pr pc mc nc K sq tq M with
  | Some (sr, si, _, _) =>
      Some (Iadd (Iadd (Iconst (Qopp (uqs sq tq))) (Iconst (1 # 2)))
              (Iadd sr (mkI (Qopp Bq) Bq)),
            Iadd (Iconst (Qopp (vqs sq tq)))
              (Iadd si (mkI (Qopp Bq) Bq)))
  | None => None
  end.

Theorem IzetaS_sound : forall p m pl pr pc mc nc K sq tq M Bq zr zi
    (H0 : 0 < Re (lineC (Q2R sq) (Q2R tq)))
    (H1 : Cminus C1 (lineC (Q2R sq) (Q2R tq)) <> C0),
  0 < Dts (Q2R sq) (Q2R tq) ->
  Kh (lineC (Q2R sq) (Q2R tq))
    * Rpower (INR (S M)) (- Re (lineC (Q2R sq) (Q2R tq))) / INR (S M)
    <= Q2R Bq ->
  IzetaS p m pl pr pc mc nc K sq tq M Bq = Some (zr, zi) ->
  Icontains zr (Re (zetaC (lineC (Q2R sq) (Q2R tq)) H0 H1))
  /\ Icontains zi (Im (zetaC (lineC (Q2R sq) (Q2R tq)) H0 H1)).
Proof.
  intros p m pl pr pc mc nc K sq tq M Bq zr zi H0 H1 HD HB H.
  unfold IzetaS in H.
  destruct (ISum2S p m pl pr pc mc nc K sq tq M)
    as [[[[sr si] Lb] qb] |] eqn:Hs; [ | discriminate ].
  injection H as <- <-.
  destruct (ISum2S_sound p m pl pr pc mc nc K sq tq M sr si Lb qb HD Hs)
    as [S1 [S2 _]].
  set (s := lineC (Q2R sq) (Q2R tq)) in *.
  set (Hs' := Hsum s H0 H1) in *.
  set (Ps := Cpsum (htermC s) M) in *.
  assert (Htail : Cmod (Cminus Hs' Ps) <= Q2R Bq).
  { eapply Rle_trans; [ apply htermC_tail | exact HB ]. }
  assert (HT : Icontains (mkI (Qopp Bq) Bq) (Re (Cminus Hs' Ps))
               /\ Icontains (mkI (Qopp Bq) Bq) (Im (Cminus Hs' Ps))).
  { pose proof (Rabs_Re_le (Cminus Hs' Ps)) as HR.
    pose proof (Rabs_Im_le (Cminus Hs' Ps)) as HI.
    pose proof (Rle_abs (Re (Cminus Hs' Ps))) as R1.
    pose proof (Rle_abs (- Re (Cminus Hs' Ps))) as R2.
    rewrite Rabs_Ropp in R2.
    pose proof (Rle_abs (Im (Cminus Hs' Ps))) as I1.
    pose proof (Rle_abs (- Im (Cminus Hs' Ps))) as I2.
    rewrite Rabs_Ropp in I2.
    split; unfold Icontains; cbn [ilo ihi]; rewrite Q2R_opp; lra. }
  destruct HT as [HTr HTi].
  rewrite (zetaC_trapezoid s H0 H1). fold Hs'.
  assert (ER : Re Hs' = Re Ps + Re (Cminus Hs' Ps))
    by (rewrite Re_Cminus; ring).
  assert (EI : Im Hs' = Im Ps + Im (Cminus Hs' Ps))
    by (rewrite Im_Cminus; ring).
  split.
  - rewrite !Re_Cadd', ER.
    apply Iadd_sound; [ apply Iadd_sound | apply Iadd_sound; assumption ].
    + unfold s. rewrite (Re_Cinv_line (Q2R sq) (Q2R tq) HD).
      replace (- ((1 - Q2R sq) / Dts (Q2R sq) (Q2R tq)))
        with (Q2R (Qopp (uqs sq tq)))
        by (rewrite Q2R_opp, (Q2R_uqs sq tq HD); reflexivity).
      apply Iconst_sound.
    + replace (Re (RtoC (/ 2))) with (Q2R (1 # 2))
        by (rewrite Q2R_phalf; reflexivity).
      apply Iconst_sound.
  - rewrite !Im_Cadd', EI.
    apply Iadd_sound; [ | apply Iadd_sound; assumption ].
    replace (Im (Cinv (Cminus s C1)) + Im (RtoC (/ 2)))
      with (Q2R (Qopp (vqs sq tq))).
    + apply Iconst_sound.
    + unfold s. rewrite (Im_Cinv_line (Q2R sq) (Q2R tq) HD), Q2R_opp,
        (Q2R_vqs sq tq HD).
      cbn [Im RtoC]. ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  The tail bound, uniform in sg >= 1/2.                              *)
(* ----------------------------------------------------------------- *)

Lemma Cmod_line_le : forall sg t, 0 <= sg -> 0 <= t ->
  Cmod (lineC sg t) <= sg + t.
Proof.
  intros sg t Hs Ht. eapply Rle_trans; [ apply Cmod_le_comp | ].
  unfold lineC; cbn [Re Im].
  rewrite (Rabs_right sg) by lra. rewrite (Rabs_right t) by lra. lra.
Qed.

Lemma Cmod_line1_le : forall sg t, 0 <= sg -> 0 <= t ->
  Cmod (Cadd (lineC sg t) C1) <= sg + 1 + t.
Proof.
  intros sg t Hs Ht. eapply Rle_trans; [ apply Cmod_le_comp | ].
  unfold lineC, Cadd, C1; cbn [Re Im].
  rewrite (Rabs_right (sg + 1)) by lra. rewrite (Rabs_right (t + 0)) by lra.
  lra.
Qed.

Theorem tail_le_S : forall sg t M r, / 2 <= sg -> 0 <= t -> 0 < r ->
  1 <= r ^ 2 * INR (S M) ->
  Kh (lineC sg t) * Rpower (INR (S M)) (- sg) / INR (S M)
  <= / 6 * ((sg + t) * (sg + 1 + t)) * r / INR (S M).
Proof.
  intros sg t M r Hsg Ht Hr H.
  assert (HN : 0 < INR (S M)) by (apply lt_0_INR; lia).
  assert (HN1 : 1 <= INR (S M)) by (replace 1 with (INR 1) by (simpl; ring);
                                    apply le_INR; lia).
  (* the sigma-uniform step: (M+1)^{-sg} <= (M+1)^{-1/2} *)
  assert (Hmono : Rpower (INR (S M)) (- sg) <= Rpower (INR (S M)) (- / 2))
    by (apply Rle_Rpower; lra).
  assert (Hp : Rpower (INR (S M)) (- / 2) = / sqrt (INR (S M))).
  { rewrite Rpower_Ropp, Rpower_sqrt by exact HN. reflexivity. }
  rewrite Hp in Hmono.
  assert (Hsq : / sqrt (INR (S M)) <= r) by (apply inv_sqrt_le; assumption).
  assert (Hpos : 0 < Rpower (INR (S M)) (- sg)) by apply exp_pos.
  assert (HK : Kh (lineC sg t) <= / 6 * ((sg + t) * (sg + 1 + t))).
  { unfold Kh.
    pose proof (Cmod_line_le sg t ltac:(lra) Ht) as C1'.
    pose proof (Cmod_line1_le sg t ltac:(lra) Ht) as C2'.
    pose proof (Cmod_nonneg (lineC sg t)) as P1.
    pose proof (Cmod_nonneg (Cadd (lineC sg t) C1)) as P2.
    assert (Hprod : Cmod (lineC sg t) * Cmod (Cadd (lineC sg t) C1)
                    <= (sg + t) * (sg + 1 + t)) by nra.
    lra. }
  assert (HK0 : 0 <= Kh (lineC sg t)) by apply Kh_nonneg.
  unfold Rdiv.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact HN | ].
  nra.
Qed.

Print Assumptions IzetaS_sound.
Print Assumptions tail_le_S.

(* ================================================================= *)
(*  END ZetaEncloseS.v -- certified zeta on any vertical line sq > 0.  *)
(* ================================================================= *)
