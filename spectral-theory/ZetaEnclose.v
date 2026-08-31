(* ================================================================= *)
(*  ZetaEnclose.v  --  a certified interval for zeta on the critical   *)
(*  line, from the trapezoid representation.                          *)
(*                                                                    *)
(*    zetaC s = 1/(s-1) + 1/2 + sum_{n<=M} htermC s n + E,            *)
(*    |E| <= Kh(s) (M+1)^{-1/2}/(M+1)          (ZetaEM.htermC_tail)   *)
(*                                                                    *)
(*  and on the critical line (ZetaCrit) every ingredient is a real     *)
(*  expression in exp, ln, cos, sin, so no complex interval type is    *)
(*  needed.  Range conditions are discharged by computation, in the    *)
(*  option style of IntervalGint.                                     *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Qreals QArith Bool.
Require Import ComplexField Cmodulus CSeries CZetaTerm CZeta CoherenceSingularity
        IntervalArith IntervalArithFun IntervalCos IntervalLn IntervalGint
        IntervalAtan IntervalTrig IntervalLnSeries LnSeries CertifiedPi ZetaCrit
        ZetaTrap ZetaEM.
Open Scope R_scope.

(* ---- guarded interval trig ---- *)

Definition Icos_itvc (p m n : nat) (j : Itv) : option Itv :=
  if inrangec m (Imid j) then Some (Icos_itv p m n j) else None.

Lemma Icos_itvc_sound : forall p m n j i x,
  Icontains j x -> Icos_itvc p m n j = Some i -> Icontains i (cos x).
Proof.
  intros p m n j i x Hx H. unfold Icos_itvc in H.
  destruct (inrangec m (Imid j)) eqn:Hg; [ | discriminate ].
  injection H as <-. unfold inrangec in Hg.
  apply andb_true_iff in Hg as [H1 H2].
  apply Qle_R in H1. apply Qle_R in H2.
  rewrite Q2R_half_scale in H1, H2.
  assert (E1 : Q2R (- (157 # 100)) = - (157 / 100)) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (157 # 100) = 157 / 100) by (unfold Q2R; simpl; lra).
  rewrite E1 in H1. rewrite E2 in H2.
  pose proof PI_lower as HP.
  apply Icos_itv_sound; [ exact Hx | lra | lra ].
Qed.

Definition Isin_itvc (p m n : nat) (j : Itv) : option Itv :=
  if inrangec m (Imid (Isub j Ihalfpi)) then Some (Isin_itv p m n j) else None.

Lemma Isin_itvc_sound : forall p m n j i x,
  Icontains j x -> Isin_itvc p m n j = Some i -> Icontains i (sin x).
Proof.
  intros p m n j i x Hx H. unfold Isin_itvc in H.
  destruct (inrangec m (Imid (Isub j Ihalfpi))) eqn:Hg; [ | discriminate ].
  injection H as <-. unfold inrangec in Hg.
  apply andb_true_iff in Hg as [H1 H2].
  apply Qle_R in H1. apply Qle_R in H2.
  rewrite Q2R_half_scale in H1, H2.
  assert (E1 : Q2R (- (157 # 100)) = - (157 / 100)) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (157 # 100) = 157 / 100) by (unfold Q2R; simpl; lra).
  rewrite E1 in H1. rewrite E2 in H2.
  pose proof PI_lower as HP.
  apply Isin_itv_sound; [ exact Hx | lra | lra ].
Qed.

(* ---- the four components at one integer ---- *)

Definition uq (tq : Q) : Q := Qdiv (1 # 2) (Qplus (1 # 4) (Qmult tq tq)).
Definition vq (tq : Q) : Q := Qdiv tq (Qplus (1 # 4) (Qmult tq tq)).

Lemma Q2R_uq : forall tq, Q2R (uq tq) = / 2 / Dt (Q2R tq).
Proof.
  intro tq. unfold uq, Dt.
  assert (Hd : ~ (Qplus (1 # 4) (Qmult tq tq) == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_plus, Q2R_mult.
    assert (E : Q2R (1 # 4) = / 4) by (unfold Q2R; simpl; lra).
    rewrite E. apply Rgt_not_eq. nra. }
  rewrite Q2R_div by exact Hd. rewrite Q2R_plus, Q2R_mult.
  assert (E : Q2R (1 # 4) = / 4) by (unfold Q2R; simpl; lra).
  assert (E2 : Q2R (1 # 2) = / 2) by (unfold Q2R; simpl; lra).
  rewrite E, E2. replace (Q2R tq ^ 2) with (Q2R tq * Q2R tq) by ring.
  reflexivity.
Qed.

Lemma Q2R_vq : forall tq, Q2R (vq tq) = Q2R tq / Dt (Q2R tq).
Proof.
  intro tq. unfold vq, Dt.
  assert (Hd : ~ (Qplus (1 # 4) (Qmult tq tq) == 0)%Q).
  { apply Qne0_of_R. rewrite Q2R_plus, Q2R_mult.
    assert (E : Q2R (1 # 4) = / 4) by (unfold Q2R; simpl; lra).
    rewrite E. apply Rgt_not_eq. nra. }
  rewrite Q2R_div by exact Hd. rewrite Q2R_plus, Q2R_mult.
  assert (E : Q2R (1 # 4) = / 4) by (unfold Q2R; simpl; lra).
  rewrite E. replace (Q2R tq ^ 2) with (Q2R tq * Q2R tq) by ring.
  reflexivity.
Qed.

Definition Iquad (p m pl pr pc mc nc K : nat) (tq : Q) (j : nat)
  : option (Itv * Itv * Itv * Itv) :=
  let L := Ilntab pl K j in
  let AR := Iround pr (Imul (Iconst tq) L) in
  match Iexp_itvc p m (Iround pr (Imul (Iconst (-1 # 2)) L)),
        Iexp_itvc p m (Iround pr (Imul (Iconst (1 # 2)) L)),
        Icos_itvc pc mc nc AR, Isin_itvc pc mc nc AR with
  | Some P, Some Qv, Some A, Some Sv =>
      Some (Imul P A,
            Ineg (Imul P Sv),
            Imul Qv (Iadd (Imul A (Iconst (uq tq))) (Imul Sv (Iconst (vq tq)))),
            Imul Qv (Isub (Imul A (Iconst (vq tq))) (Imul Sv (Iconst (uq tq)))))
  | _, _, _, _ => None
  end.

Lemma Q2R_mhalf : Q2R (-1 # 2) = - (/ 2).
Proof. unfold Q2R; simpl; lra. Qed.

Lemma Q2R_phalf : Q2R (1 # 2) = / 2.
Proof. unfold Q2R; simpl; lra. Qed.

Theorem Iquad_sound : forall p m pl pr pc mc nc K tq j rg ig rG iG,
  (1 <= j)%nat ->
  Iquad p m pl pr pc mc nc K tq j = Some (rg, ig, rG, iG) ->
  Icontains rg (Re (gC (crit (Q2R tq)) (INR j)))
  /\ Icontains ig (Im (gC (crit (Q2R tq)) (INR j)))
  /\ Icontains rG (Re (GC (crit (Q2R tq)) (INR j)))
  /\ Icontains iG (Im (GC (crit (Q2R tq)) (INR j))).
Proof.
  intros p m pl pr pc mc nc K tq j rg ig rG iG Hj H.
  unfold Iquad in H.
  set (L := Ilntab pl K j) in *.
  set (AR := Iround pr (Imul (Iconst tq) L)) in *.
  assert (HL : Icontains L (ln (INR j))) by (apply Ilntab_sound; exact Hj).
  assert (HAR : Icontains AR (Q2R tq * ln (INR j))).
  { unfold AR. apply Iround_sound, Imul_sound;
      [ apply Iconst_sound | exact HL ]. }
  destruct (Iexp_itvc p m (Iround pr (Imul (Iconst (-1 # 2)) L))) eqn:HP;
    [ | discriminate ].
  destruct (Iexp_itvc p m (Iround pr (Imul (Iconst (1 # 2)) L))) eqn:HQ;
    [ | discriminate ].
  destruct (Icos_itvc pc mc nc AR) eqn:HA; [ | discriminate ].
  destruct (Isin_itvc pc mc nc AR) eqn:HS; [ | discriminate ].
  injection H as <- <- <- <-.
  assert (HPc : Icontains i (exp (- (/ 2) * ln (INR j)))).
  { eapply Iexp_itvc_sound; [ exact HP | ].
    rewrite <- Q2R_mhalf. apply Iround_sound, Imul_sound;
      [ apply Iconst_sound | exact HL ]. }
  assert (HQc : Icontains i0 (exp (/ 2 * ln (INR j)))).
  { eapply Iexp_itvc_sound; [ exact HQ | ].
    rewrite <- Q2R_phalf. apply Iround_sound, Imul_sound;
      [ apply Iconst_sound | exact HL ]. }
  assert (HAc : Icontains i1 (cos (Q2R tq * ln (INR j))))
    by (apply (Icos_itvc_sound pc mc nc AR); assumption).
  assert (HSc : Icontains i2 (sin (Q2R tq * ln (INR j))))
    by (apply (Isin_itvc_sound pc mc nc AR); assumption).
  refine (conj _ (conj _ (conj _ _))).
  - rewrite Re_gC_crit. apply Imul_sound; assumption.
  - rewrite Im_gC_crit. apply Ineg_sound. apply Imul_sound; assumption.
  - rewrite Re_GC_crit. apply Imul_sound; [ exact HQc | ].
    apply Iadd_sound; apply Imul_sound; try assumption;
      [ rewrite <- Q2R_uq; apply Iconst_sound
      | rewrite <- Q2R_vq; apply Iconst_sound ].
  - rewrite Im_GC_crit. apply Imul_sound; [ exact HQc | ].
    apply Isub_sound; apply Imul_sound; try assumption;
      [ rewrite <- Q2R_vq; apply Iconst_sound
      | rewrite <- Q2R_uq; apply Iconst_sound ].
Qed.

(* ---- the trapezoid term ---- *)

Lemma Re_htermC : forall s n,
  Re (htermC s n)
  = / 2 * (Re (gC s (INR (S n))) + Re (gC s (INR (S (S n)))))
    - (Re (GC s (INR (S (S n)))) - Re (GC s (INR (S n)))).
Proof.
  intros s n. unfold htermC. rewrite !Re_Cminus, Re_scal, Re_Cadd'.
  reflexivity.
Qed.

Lemma Im_htermC : forall s n,
  Im (htermC s n)
  = / 2 * (Im (gC s (INR (S n))) + Im (gC s (INR (S (S n)))))
    - (Im (GC s (INR (S (S n)))) - Im (GC s (INR (S n)))).
Proof.
  intros s n. unfold htermC. rewrite !Im_Cminus, Im_scal, Im_Cadd'.
  reflexivity.
Qed.

Definition IH (p m pl pr pc mc nc K : nat) (tq : Q) (n : nat)
  : option (Itv * Itv) :=
  match Iquad p m pl pr pc mc nc K tq (S n),
        Iquad p m pl pr pc mc nc K tq (S (S n)) with
  | Some (ra, ia, Ra, Ia), Some (rb, ib, Rb, Ib) =>
      Some (Isub (Imul (Iconst (1 # 2)) (Iadd ra rb)) (Isub Rb Ra),
            Isub (Imul (Iconst (1 # 2)) (Iadd ia ib)) (Isub Ib Ia))
  | _, _ => None
  end.

Lemma IH_sound : forall p m pl pr pc mc nc K tq n hr hi,
  IH p m pl pr pc mc nc K tq n = Some (hr, hi) ->
  Icontains hr (Re (htermC (crit (Q2R tq)) n))
  /\ Icontains hi (Im (htermC (crit (Q2R tq)) n)).
Proof.
  intros p m pl pr pc mc nc K tq n hr hi H. unfold IH in H.
  destruct (Iquad p m pl pr pc mc nc K tq (S n))
    as [[[[ra ia] Ra] Ia] |] eqn:Ha; [ | discriminate ].
  destruct (Iquad p m pl pr pc mc nc K tq (S (S n)))
    as [[[[rb ib] Rb] Ib] |] eqn:Hb; [ | discriminate ].
  injection H as <- <-.
  destruct (Iquad_sound p m pl pr pc mc nc K tq (S n) ra ia Ra Ia
              ltac:(lia) Ha) as [A1 [A2 [A3 A4]]].
  destruct (Iquad_sound p m pl pr pc mc nc K tq (S (S n)) rb ib Rb Ib
              ltac:(lia) Hb) as [B1 [B2 [B3 B4]]].
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

(* ---- the truncated sum ---- *)

Fixpoint ISum (p m pl pr pc mc nc K : nat) (tq : Q) (M : nat)
  : option (Itv * Itv) :=
  match M with
  | O => IH p m pl pr pc mc nc K tq 0
  | S k =>
      match ISum p m pl pr pc mc nc K tq k,
            IH p m pl pr pc mc nc K tq (S k) with
      | Some (ar, ai), Some (br, bi) =>
          Some (Iround pr (Iadd ar br), Iround pr (Iadd ai bi))
      | _, _ => None
      end
  end.

Lemma ISum_sound : forall p m pl pr pc mc nc K tq M sr si,
  ISum p m pl pr pc mc nc K tq M = Some (sr, si) ->
  Icontains sr (Re (Cpsum (htermC (crit (Q2R tq))) M))
  /\ Icontains si (Im (Cpsum (htermC (crit (Q2R tq))) M)).
Proof.
  intros p m pl pr pc mc nc K tq M. induction M as [| M IH0]; intros sr si H.
  - cbn [ISum] in H. cbn [Cpsum].
    apply (IH_sound p m pl pr pc mc nc K tq 0 sr si). exact H.
  - cbn [ISum] in H.
    destruct (ISum p m pl pr pc mc nc K tq M) as [[ar ai] |] eqn:Hs;
      [ | discriminate ].
    destruct (IH p m pl pr pc mc nc K tq (S M)) as [[br bi] |] eqn:Hh;
      [ | discriminate ].
    injection H as <- <-.
    destruct (IH0 ar ai eq_refl) as [S1 S2].
    destruct (IH_sound _ _ _ _ _ _ _ _ _ _ _ _ Hh) as [T1 T2].
    cbn [Cpsum]. split.
    + rewrite Re_Cadd'. apply Iround_sound, Iadd_sound; assumption.
    + rewrite Im_Cadd'. apply Iround_sound, Iadd_sound; assumption.
Qed.

(* ---- the head 1/(s-1) ---- *)

Lemma Re_Cinv_crit : forall t, Re (Cinv (Cminus (crit t) C1)) = - (/ 2 / Dt t).
Proof.
  intro t. pose proof (Dt_pos t) as HD.
  unfold Cinv, Cminus, crit, C1, Cnorm2; cbn [Re Im]. unfold Dt in *.
  field; repeat split; apply Rgt_not_eq; nra.
Qed.

Lemma Im_Cinv_crit : forall t, Im (Cinv (Cminus (crit t) C1)) = - (t / Dt t).
Proof.
  intro t. pose proof (Dt_pos t) as HD.
  unfold Cinv, Cminus, crit, C1, Cnorm2; cbn [Re Im]. unfold Dt in *.
  field; repeat split; apply Rgt_not_eq; nra.
Qed.

(* ---- zeta ---- *)

Definition Izeta (p m pl pr pc mc nc K : nat) (tq : Q) (M : nat) (Bq : Q)
  : option (Itv * Itv) :=
  match ISum p m pl pr pc mc nc K tq M with
  | Some (sr, si) =>
      Some (Iadd (Iadd (Iconst (Qopp (uq tq))) (Iconst (1 # 2)))
              (Iadd sr (mkI (Qopp Bq) Bq)),
            Iadd (Iconst (Qopp (vq tq)))
              (Iadd si (mkI (Qopp Bq) Bq)))
  | None => None
  end.

Theorem Izeta_sound : forall p m pl pr pc mc nc K tq M Bq zr zi
    (H0 : 0 < Re (crit (Q2R tq))) (H1 : Cminus C1 (crit (Q2R tq)) <> C0),
  Kh (crit (Q2R tq)) * Rpower (INR (S M)) (- Re (crit (Q2R tq))) / INR (S M)
    <= Q2R Bq ->
  Izeta p m pl pr pc mc nc K tq M Bq = Some (zr, zi) ->
  Icontains zr (Re (zetaC (crit (Q2R tq)) H0 H1))
  /\ Icontains zi (Im (zetaC (crit (Q2R tq)) H0 H1)).
Proof.
  intros p m pl pr pc mc nc K tq M Bq zr zi H0 H1 HB H.
  unfold Izeta in H.
  destruct (ISum p m pl pr pc mc nc K tq M) as [[sr si] |] eqn:Hs;
    [ | discriminate ].
  injection H as <- <-.
  destruct (ISum_sound p m pl pr pc mc nc K tq M sr si Hs) as [S1 S2].
  set (s := crit (Q2R tq)) in *.
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
    + unfold s. rewrite Re_Cinv_crit.
      replace (- (/ 2 / Dt (Q2R tq))) with (Q2R (Qopp (uq tq)))
        by (rewrite Q2R_opp, Q2R_uq; reflexivity).
      apply Iconst_sound.
    + replace (Re (RtoC (/ 2))) with (Q2R (1 # 2))
        by (rewrite Q2R_phalf; reflexivity).
      apply Iconst_sound.
  - rewrite !Im_Cadd', EI.
    apply Iadd_sound; [ | apply Iadd_sound; assumption ].
    replace (Im (Cinv (Cminus s C1)) + Im (RtoC (/ 2)))
      with (Q2R (Qopp (vq tq))).
    + apply Iconst_sound.
    + unfold s. rewrite Im_Cinv_crit, Q2R_opp, Q2R_vq.
      cbn [Im RtoC]. ring.
Qed.

(* ================================================================= *)
(*  Linear-cost version: thread the ln accumulator through the sum.   *)
(*                                                                    *)
(*  Iquad recomputes Ilntab from scratch at every index, so ISum is    *)
(*  O(M^2) -- 4m43s already at M = 20.  Here the log enclosure and the *)
(*  four components at the right-hand endpoint are carried forward,    *)
(*  so each step costs one ln increment and one set of transcendentals.*)
(* ================================================================= *)

Definition Lnext (pl K : nat) (j : nat) (L : Itv) : Itv :=
  Iround pl (Iadd L (Ilnstep K j)).

Lemma Lnext_sound : forall pl K j L, (1 <= j)%nat ->
  Icontains L (ln (INR j)) -> Icontains (Lnext pl K j L) (ln (INR (S j))).
Proof.
  intros pl K j L Hj HL.
  assert (Hpos : 0 < INR j) by (apply lt_0_INR; lia).
  assert (Ha : 0 < INR (S j)) by (apply lt_0_INR; lia).
  assert (E : ln (INR (S j)) = ln (INR j) + ln (INR (S j) / INR j))
    by (rewrite <- (ln_quot2 _ _ Ha Hpos); ring).
  rewrite E. apply Iround_sound, Iadd_sound;
    [ exact HL | apply Ilnstep_sound; exact Hj ].
Qed.

Definition Iquad' (p m pr pc mc nc : nat) (tq : Q) (L : Itv)
  : option (Itv * Itv * Itv * Itv) :=
  let AR := Iround pr (Imul (Iconst tq) L) in
  match Iexp_itvc p m (Iround pr (Imul (Iconst (-1 # 2)) L)),
        Iexp_itvc p m (Iround pr (Imul (Iconst (1 # 2)) L)),
        Icos_itvc pc mc nc AR, Isin_itvc pc mc nc AR with
  | Some P, Some Qv, Some A, Some Sv =>
      Some (Imul P A,
            Ineg (Imul P Sv),
            Imul Qv (Iadd (Imul A (Iconst (uq tq))) (Imul Sv (Iconst (vq tq)))),
            Imul Qv (Isub (Imul A (Iconst (vq tq))) (Imul Sv (Iconst (uq tq)))))
  | _, _, _, _ => None
  end.

Definition QuadOK (tq : Q) (x : R) (q : Itv * Itv * Itv * Itv) : Prop :=
  let '(rg, ig, rG, iG) := q in
  Icontains rg (Re (gC (crit (Q2R tq)) x))
  /\ Icontains ig (Im (gC (crit (Q2R tq)) x))
  /\ Icontains rG (Re (GC (crit (Q2R tq)) x))
  /\ Icontains iG (Im (GC (crit (Q2R tq)) x)).

Lemma Iquad'_sound : forall p m pr pc mc nc tq L x q,
  Icontains L (ln x) ->
  Iquad' p m pr pc mc nc tq L = Some q -> QuadOK tq x q.
Proof.
  intros p m pr pc mc nc tq L x q HL H. unfold Iquad' in H.
  set (AR := Iround pr (Imul (Iconst tq) L)) in *.
  assert (HAR : Icontains AR (Q2R tq * ln x))
    by (unfold AR; apply Iround_sound, Imul_sound;
        [ apply Iconst_sound | exact HL ]).
  destruct (Iexp_itvc p m (Iround pr (Imul (Iconst (-1 # 2)) L))) eqn:HP;
    [ | discriminate ].
  destruct (Iexp_itvc p m (Iround pr (Imul (Iconst (1 # 2)) L))) eqn:HQ;
    [ | discriminate ].
  destruct (Icos_itvc pc mc nc AR) eqn:HA; [ | discriminate ].
  destruct (Isin_itvc pc mc nc AR) eqn:HS; [ | discriminate ].
  injection H as <-.
  assert (HPc : Icontains i (exp (- (/ 2) * ln x))).
  { eapply Iexp_itvc_sound; [ exact HP | ].
    rewrite <- Q2R_mhalf. apply Iround_sound, Imul_sound;
      [ apply Iconst_sound | exact HL ]. }
  assert (HQc : Icontains i0 (exp (/ 2 * ln x))).
  { eapply Iexp_itvc_sound; [ exact HQ | ].
    rewrite <- Q2R_phalf. apply Iround_sound, Imul_sound;
      [ apply Iconst_sound | exact HL ]. }
  assert (HAc : Icontains i1 (cos (Q2R tq * ln x)))
    by (apply (Icos_itvc_sound pc mc nc AR); assumption).
  assert (HSc : Icontains i2 (sin (Q2R tq * ln x)))
    by (apply (Isin_itvc_sound pc mc nc AR); assumption).
  unfold QuadOK. refine (conj _ (conj _ (conj _ _))).
  - rewrite Re_gC_crit. apply Imul_sound; assumption.
  - rewrite Im_gC_crit. apply Ineg_sound. apply Imul_sound; assumption.
  - rewrite Re_GC_crit. apply Imul_sound; [ exact HQc | ].
    apply Iadd_sound; apply Imul_sound; try assumption;
      [ rewrite <- Q2R_uq; apply Iconst_sound
      | rewrite <- Q2R_vq; apply Iconst_sound ].
  - rewrite Im_GC_crit. apply Imul_sound; [ exact HQc | ].
    apply Isub_sound; apply Imul_sound; try assumption;
      [ rewrite <- Q2R_vq; apply Iconst_sound
      | rewrite <- Q2R_uq; apply Iconst_sound ].
Qed.

Definition mkterm (a b : Itv * Itv * Itv * Itv) : Itv * Itv :=
  let '(ra, ia, Ra, Ia) := a in
  let '(rb, ib, Rb, Ib) := b in
  (Isub (Imul (Iconst (1 # 2)) (Iadd ra rb)) (Isub Rb Ra),
   Isub (Imul (Iconst (1 # 2)) (Iadd ia ib)) (Isub Ib Ia)).

Lemma mkterm_sound : forall tq n qa qb tr ti,
  QuadOK tq (INR (S n)) qa -> QuadOK tq (INR (S (S n))) qb ->
  mkterm qa qb = (tr, ti) ->
  Icontains tr (Re (htermC (crit (Q2R tq)) n))
  /\ Icontains ti (Im (htermC (crit (Q2R tq)) n)).
Proof.
  intros tq n [[[ra ia] Ra] Ia] [[[rb ib] Rb] Ib] tr ti
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

Fixpoint ISum2 (p m pl pr pc mc nc K : nat) (tq : Q) (M : nat)
  : option (Itv * Itv * Itv * (Itv * Itv * Itv * Itv)) :=
  match M with
  | O =>
      match Iquad' p m pr pc mc nc tq (Iconst 0),
            Iquad' p m pr pc mc nc tq (Lnext pl K 1 (Iconst 0)) with
      | Some q1, Some q2 =>
          match mkterm q1 q2 with
          | (tr, ti) => Some (tr, ti, Lnext pl K 1 (Iconst 0), q2)
          end
      | _, _ => None
      end
  | S k =>
      match ISum2 p m pl pr pc mc nc K tq k with
      | Some (r, i, Lb, qb) =>
          match Iquad' p m pr pc mc nc tq (Lnext pl K (S (S k)) Lb) with
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

Lemma ISum2_sound : forall p m pl pr pc mc nc K tq M r i Lb qb,
  ISum2 p m pl pr pc mc nc K tq M = Some (r, i, Lb, qb) ->
  Icontains r (Re (Cpsum (htermC (crit (Q2R tq))) M))
  /\ Icontains i (Im (Cpsum (htermC (crit (Q2R tq))) M))
  /\ Icontains Lb (ln (INR (S (S M))))
  /\ QuadOK tq (INR (S (S M))) qb.
Proof.
  intros p m pl pr pc mc nc K tq M.
  induction M as [| M IH0]; intros r i Lb qb H.
  - cbn [ISum2] in H.
    assert (HL1 : Icontains (Iconst 0) (ln (INR 1))).
    { replace (INR 1) with 1 by (simpl; ring). rewrite ln_1.
      replace 0 with (Q2R 0) by apply Q2R_zero. apply Iconst_sound. }
    assert (HL2 : Icontains (Lnext pl K 1 (Iconst 0)) (ln (INR 2)))
      by (apply (Lnext_sound pl K 1); [ lia | exact HL1 ]).
    destruct (Iquad' p m pr pc mc nc tq (Iconst 0)) as [q1 |] eqn:Hq1;
      [ | discriminate ].
    destruct (Iquad' p m pr pc mc nc tq (Lnext pl K 1 (Iconst 0)))
      as [q2 |] eqn:Hq2; [ | discriminate ].
    destruct (mkterm q1 q2) as [tr ti] eqn:Hm.
    injection H as <- <- <- <-.
    assert (Q1 : QuadOK tq (INR 1) q1)
      by (apply (Iquad'_sound p m pr pc mc nc tq (Iconst 0)); assumption).
    assert (Q2 : QuadOK tq (INR 2) q2)
      by (apply (Iquad'_sound p m pr pc mc nc tq (Lnext pl K 1 (Iconst 0)));
          assumption).
    destruct (mkterm_sound tq 0 q1 q2 tr ti Q1 Q2 Hm) as [T1 T2].
    cbn [Cpsum]. exact (conj T1 (conj T2 (conj HL2 Q2))).
  - cbn [ISum2] in H.
    destruct (ISum2 p m pl pr pc mc nc K tq M) as [[[[r0 i0] Lb0] qb0] |]
      eqn:Hs; [ | discriminate ].
    destruct (IH0 r0 i0 Lb0 qb0 eq_refl) as [S1 [S2 [S3 S4]]].
    destruct (Iquad' p m pr pc mc nc tq (Lnext pl K (S (S M)) Lb0))
      as [qc |] eqn:Hqc; [ | discriminate ].
    destruct (mkterm qb0 qc) as [tr ti] eqn:Hm.
    injection H as <- <- <- <-.
    assert (HLc : Icontains (Lnext pl K (S (S M)) Lb0) (ln (INR (S (S (S M))))))
      by (apply (Lnext_sound pl K (S (S M))); [ lia | exact S3 ]).
    assert (Qc : QuadOK tq (INR (S (S (S M)))) qc)
      by (apply (Iquad'_sound p m pr pc mc nc tq
                   (Lnext pl K (S (S M)) Lb0)); assumption).
    destruct (mkterm_sound tq (S M) qb0 qc tr ti S4 Qc Hm) as [T1 T2].
    cbn [Cpsum].
    refine (conj _ (conj _ (conj HLc Qc))).
    + rewrite Re_Cadd'. apply Iround_sound, Iadd_sound; assumption.
    + rewrite Im_Cadd'. apply Iround_sound, Iadd_sound; assumption.
Qed.

Definition Izeta2 (p m pl pr pc mc nc K : nat) (tq : Q) (M : nat) (Bq : Q)
  : option (Itv * Itv) :=
  match ISum2 p m pl pr pc mc nc K tq M with
  | Some (sr, si, _, _) =>
      Some (Iadd (Iadd (Iconst (Qopp (uq tq))) (Iconst (1 # 2)))
              (Iadd sr (mkI (Qopp Bq) Bq)),
            Iadd (Iconst (Qopp (vq tq)))
              (Iadd si (mkI (Qopp Bq) Bq)))
  | None => None
  end.

Theorem Izeta2_sound : forall p m pl pr pc mc nc K tq M Bq zr zi
    (H0 : 0 < Re (crit (Q2R tq))) (H1 : Cminus C1 (crit (Q2R tq)) <> C0),
  Kh (crit (Q2R tq)) * Rpower (INR (S M)) (- Re (crit (Q2R tq))) / INR (S M)
    <= Q2R Bq ->
  Izeta2 p m pl pr pc mc nc K tq M Bq = Some (zr, zi) ->
  Icontains zr (Re (zetaC (crit (Q2R tq)) H0 H1))
  /\ Icontains zi (Im (zetaC (crit (Q2R tq)) H0 H1)).
Proof.
  intros p m pl pr pc mc nc K tq M Bq zr zi H0 H1 HB H.
  unfold Izeta2 in H.
  destruct (ISum2 p m pl pr pc mc nc K tq M) as [[[[sr si] Lb] qb] |] eqn:Hs;
    [ | discriminate ].
  injection H as <- <-.
  destruct (ISum2_sound p m pl pr pc mc nc K tq M sr si Lb qb Hs)
    as [S1 [S2 _]].
  set (s := crit (Q2R tq)) in *.
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
    + unfold s. rewrite Re_Cinv_crit.
      replace (- (/ 2 / Dt (Q2R tq))) with (Q2R (Qopp (uq tq)))
        by (rewrite Q2R_opp, Q2R_uq; reflexivity).
      apply Iconst_sound.
    + replace (Re (RtoC (/ 2))) with (Q2R (1 # 2))
        by (rewrite Q2R_phalf; reflexivity).
      apply Iconst_sound.
  - rewrite !Im_Cadd', EI.
    apply Iadd_sound; [ | apply Iadd_sound; assumption ].
    replace (Im (Cinv (Cminus s C1)) + Im (RtoC (/ 2)))
      with (Q2R (Qopp (vq tq))).
    + apply Iconst_sound.
    + unfold s. rewrite Im_Cinv_crit, Q2R_opp, Q2R_vq.
      cbn [Im RtoC]. ring.
Qed.

(* ================================================================= *)
(*  Discharging the tail bound.                                       *)
(*                                                                    *)
(*  Kh(s) = (1/6)|s||s+1| with s = 1/2+it, and Re s = 1/2, so the      *)
(*  bound in htermC_tail is (1/6)|s||s+1| / (sqrt(M+1) (M+1)).  Both   *)
(*  moduli are bounded by |Re| + |Im|, and 1/sqrt(M+1) <= r for any    *)
(*  rational r with r^2 (M+1) >= 1 -- so the whole thing is rational   *)
(*  arithmetic, with no square root ever computed.                    *)
(* ================================================================= *)

Lemma Cmod_crit_le : forall t, 0 <= t -> Cmod (crit t) <= / 2 + t.
Proof.
  intros t Ht. eapply Rle_trans; [ apply Cmod_le_comp | ].
  unfold crit; cbn [Re Im].
  rewrite (Rabs_right (/ 2)) by lra. rewrite (Rabs_right t) by lra. lra.
Qed.

Lemma Cmod_crit1_le : forall t, 0 <= t ->
  Cmod (Cadd (crit t) C1) <= 3 / 2 + t.
Proof.
  intros t Ht. eapply Rle_trans; [ apply Cmod_le_comp | ].
  unfold crit, Cadd, C1; cbn [Re Im].
  rewrite (Rabs_right (/ 2 + 1)) by lra. rewrite (Rabs_right (t + 0)) by lra.
  lra.
Qed.

Lemma inv_sqrt_le : forall N r, 0 < N -> 0 < r -> 1 <= r ^ 2 * N ->
  / sqrt N <= r.
Proof.
  intros N r HN Hr H.
  assert (Hs : 0 < sqrt N) by (apply sqrt_lt_R0; exact HN).
  assert (Hsq : sqrt N * sqrt N = N) by (apply sqrt_sqrt; lra).
  assert (Hge : 1 <= r * sqrt N).
  { assert (Hp : 0 < r * sqrt N) by (apply Rmult_lt_0_compat; lra).
    nra. }
  apply Rmult_le_reg_r with (sqrt N); [ exact Hs | ].
  rewrite Rinv_l by lra. lra.
Qed.

Theorem tail_le : forall t M r, 0 <= t -> 0 < r ->
  1 <= r ^ 2 * INR (S M) ->
  Kh (crit t) * Rpower (INR (S M)) (- Re (crit t)) / INR (S M)
  <= / 6 * ((/ 2 + t) * (3 / 2 + t)) * r / INR (S M).
Proof.
  intros t M r Ht Hr H.
  assert (HN : 0 < INR (S M)) by (apply lt_0_INR; lia).
  assert (HRe : Re (crit t) = / 2) by reflexivity.
  rewrite HRe.
  assert (Hp : Rpower (INR (S M)) (- / 2) = / sqrt (INR (S M))).
  { rewrite Rpower_Ropp, Rpower_sqrt by exact HN. reflexivity. }
  rewrite Hp.
  assert (Hsq : / sqrt (INR (S M)) <= r) by (apply inv_sqrt_le; assumption).
  assert (Hsq0 : 0 < / sqrt (INR (S M))).
  { apply Rinv_0_lt_compat, sqrt_lt_R0; exact HN. }
  assert (HK : Kh (crit t) <= / 6 * ((/ 2 + t) * (3 / 2 + t))).
  { unfold Kh.
    pose proof (Cmod_crit_le t Ht) as C1'.
    pose proof (Cmod_crit1_le t Ht) as C2'.
    pose proof (Cmod_nonneg (crit t)) as P1.
    pose proof (Cmod_nonneg (Cadd (crit t) C1)) as P2.
    assert (Hprod : Cmod (crit t) * Cmod (Cadd (crit t) C1)
                    <= (/ 2 + t) * (3 / 2 + t)) by nra.
    lra. }
  assert (HK0 : 0 <= Kh (crit t)) by apply Kh_nonneg.
  unfold Rdiv.
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact HN | ].
  nra.
Qed.
