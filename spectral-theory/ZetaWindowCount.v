(* ================================================================= *)
(*  ZetaWindowCount.v  --  zeros of zeta in a window at height T.      *)
(*                                                                    *)
(*  Part 1: the reflection rho |-> 1 - conj rho, and the halving it    *)
(*  buys.                                                             *)
(*                                                                    *)
(*  WHY HALVING IS MANDATORY, not an optimisation.  The peel disk is   *)
(*  centred at 11/10 + i t and must reach the zero.  Reaching Re = 1/2 *)
(*  needs count radius 3/5; reaching Re near 0 would need radius > 1,  *)
(*  hence (count radius < R/2) a bound circle of radius > 2, whose     *)
(*  left edge is below Re s = -1 -- outside where Bfn1 exists at all.  *)
(*  So the count is taken only over zeros with Re >= 1/2, and the      *)
(*  reflection doubles it to cover the strip.                         *)
(*                                                                    *)
(*  The reflection preserves Im, which is what makes it usable for a   *)
(*  count localized in HEIGHT.                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CSeries CDeriv Holomorphic
        CZeta ZetaFn RiemannXiEntire ZetaOpenStrip GammaCNe0
        ZetaZeroPairing ZetaZeroQuadruple CSeries CPathIntegral
        ZetaEM ZetaEMExt ZetaEMExtHolo ZetaStripBound ZetaLowerBound
        CPeelBoundGen CPeelAtCentre CHoloCalculus.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  1.  the reflection                                                 *)
(* ----------------------------------------------------------------- *)

Definition refl1 (z : C) : C := Cminus C1 (Cconj z).

Lemma Re_refl1 : forall z, Re (refl1 z) = 1 - Re z.
Proof. intro z. unfold refl1, Cminus, Cconj, Copp, C1; cbn; ring. Qed.

Lemma Im_refl1 : forall z, Im (refl1 z) = Im z.
Proof. intro z. unfold refl1, Cminus, Cconj, Copp, C1; cbn; ring. Qed.

Lemma refl1_invol : forall z, refl1 (refl1 z) = z.
Proof. intro z. unfold refl1, Cminus, Cconj, Copp, C1; apply Ceq; cbn; ring. Qed.

Lemma refl1_inj : forall z w, refl1 z = refl1 w -> z = w.
Proof.
  intros z w H.
  rewrite <- (refl1_invol z), <- (refl1_invol w), H. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  2.  it maps zeros of zF to zeros of zF                             *)
(* ----------------------------------------------------------------- *)

Lemma strip_ne1 : forall z, 0 < Re z -> Re z < 1 -> Cminus C1 z <> C0.
Proof.
  intros z H0 H1 Hc.
  assert (HR : Re (Cminus C1 z) = 1 - Re z)
    by (unfold Cminus, Copp, C1; cbn; ring).
  rewrite Hc in HR. cbn in HR. lra.
Qed.

Lemma zF_zero_XiC : forall z, 0 < Re z -> Re z < 1 -> zF z = C0 -> XiC z = C0.
Proof.
  intros z H0 H1 Hz.
  assert (Hne : Cminus C1 z <> C0) by (apply strip_ne1; assumption).
  apply (XiC_zero_iff_zetaC_zero_final z H0 Hne H1).
  rewrite <- (zF_eq z H0 Hne). exact Hz.
Qed.

Lemma XiC_zero_zF : forall z, 0 < Re z -> Re z < 1 -> XiC z = C0 -> zF z = C0.
Proof.
  intros z H0 H1 Hz.
  assert (Hne : Cminus C1 z <> C0) by (apply strip_ne1; assumption).
  rewrite (zF_eq z H0 Hne).
  apply (XiC_zero_iff_zetaC_zero_final z H0 Hne H1). exact Hz.
Qed.

Theorem zF_zero_refl1 : forall z, 0 < Re z -> Re z < 1 -> zF z = C0 ->
  zF (refl1 z) = C0.
Proof.
  intros z H0 H1 Hz.
  assert (HX : XiC z = C0) by (apply zF_zero_XiC; assumption).
  assert (HC : XiC (Cconj z) = C0) by (apply XiC_zero_conj; exact HX).
  assert (HR : XiC (refl1 z) = C0)
    by (unfold refl1; apply XiC_zero_reflect; exact HC).
  apply XiC_zero_zF; [ rewrite Re_refl1; lra | rewrite Re_refl1; lra | exact HR ].
Qed.

(* ----------------------------------------------------------------- *)
(*  3.  the halving, at the level of lists                             *)
(* ----------------------------------------------------------------- *)

Definition rhalf (z : C) : bool :=
  if Rle_dec (/ 2) (Re z) then true else false.

Lemma NoDup_map_injective : forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd. induction Hnd as [| a l Ha Hnd IH]; cbn [map].
  - constructor.
  - constructor; [ | exact IH ].
    intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Hx Hxin]].
    apply Hinj in Hx. subst x. contradiction.
Qed.

Lemma filter_split_length : forall (A : Type) (f : A -> bool) (l : list A),
  (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat
  = length l.
Proof.
  intros A f l. induction l as [| a l IH]; [ reflexivity | ].
  cbn [filter length]. destruct (f a); cbn [length negb filter]; lia.
Qed.

Lemma refl1_zero_in_strip : forall z, 0 < Re z -> Re z < 1 -> zF z = C0 ->
  zF (refl1 z) = C0 /\ 0 < Re (refl1 z) /\ Re (refl1 z) < 1
  /\ Im (refl1 z) = Im z.
Proof.
  intros z H0 H1 Hz.
  split; [ apply zF_zero_refl1; assumption | ].
  rewrite Re_refl1, Im_refl1. repeat split; lra.
Qed.

(* if every NoDup list of zeros with Re >= 1/2 in the window is short,
   then so is every NoDup list of zeros in the whole strip *)
Theorem halve_count : forall (tj : R) (N : nat) (L : list C),
  NoDup L ->
  (forall z, In z L ->
     zF z = C0 /\ 0 < Re z /\ Re z < 1 /\ Rabs (Im z - tj) <= 11 / 20) ->
  (forall M, NoDup M ->
     (forall z, In z M ->
        zF z = C0 /\ / 2 <= Re z /\ Re z < 1 /\ Rabs (Im z - tj) <= 11 / 20) ->
     (length M <= N)%nat) ->
  (length L <= 2 * N)%nat.
Proof.
  intros tj N L Hnd Hz Hbd.
  set (L1 := filter rhalf L).
  set (L2 := filter (fun x => negb (rhalf x)) L).
  assert (Hsplit : (length L1 + length L2)%nat = length L)
    by (unfold L1, L2; apply filter_split_length).
  (* the right half is directly bounded *)
  assert (H1 : (length L1 <= N)%nat).
  { apply Hbd.
    - unfold L1; apply NoDup_filter; exact Hnd.
    - intros z Hin. unfold L1 in Hin. apply filter_In in Hin.
      destruct Hin as [HinL Hf].
      destruct (Hz z HinL) as [Hz0 [Hr0 [Hr1 Hw]]].
      unfold rhalf in Hf. destruct (Rle_dec (/ 2) (Re z)) as [Hh | Hh];
        [ | discriminate ].
      repeat split; assumption. }
  (* the left half reflects into the right half *)
  assert (H2 : (length L2 <= N)%nat).
  { assert (Hmap : (length (map refl1 L2) = length L2)%nat) by apply length_map.
    rewrite <- Hmap. apply Hbd.
    - apply NoDup_map_injective;
        [ intros x y HE; apply refl1_inj; exact HE
        | unfold L2; apply NoDup_filter; exact Hnd ].
    - intros z Hin. apply in_map_iff in Hin.
      destruct Hin as [w [Hwz Hw2]]; subst z.
      unfold L2 in Hw2. apply filter_In in Hw2.
      destruct Hw2 as [HinL Hf].
      destruct (Hz w HinL) as [Hz0 [Hr0 [Hr1 Hwin]]].
      unfold rhalf in Hf. destruct (Rle_dec (/ 2) (Re w)) as [Hh | Hh];
        [ discriminate | ].
      destruct (refl1_zero_in_strip w Hr0 Hr1 Hz0) as [Ha [Hb [Hc Hd]]].
      repeat split; try assumption.
      + rewrite Re_refl1. lra.
      + rewrite Hd. exact Hwin. }
  lia.
Qed.

(* the halving, stated with a REAL bound (the peel gives a real bound,
   not a natural one) *)
Theorem halve_count_R : forall (tj B : R) (L : list C),
  NoDup L ->
  (forall z, In z L ->
     zF z = C0 /\ 0 < Re z /\ Re z < 1 /\ Rabs (Im z - tj) <= 11 / 20) ->
  (forall M, NoDup M ->
     (forall z, In z M ->
        zF z = C0 /\ / 2 <= Re z /\ Re z < 1 /\ Rabs (Im z - tj) <= 11 / 20) ->
     INR (length M) <= B) ->
  INR (length L) <= 2 * B.
Proof.
  intros tj B L Hnd Hz Hbd.
  set (L1 := filter rhalf L).
  set (L2 := filter (fun x => negb (rhalf x)) L).
  assert (Hsplit : (length L1 + length L2)%nat = length L)
    by (unfold L1, L2; apply filter_split_length).
  assert (H1 : INR (length L1) <= B).
  { apply Hbd.
    - unfold L1; apply NoDup_filter; exact Hnd.
    - intros z Hin. unfold L1 in Hin. apply filter_In in Hin.
      destruct Hin as [HinL Hf].
      destruct (Hz z HinL) as [Hz0 [Hr0 [Hr1 Hw]]].
      unfold rhalf in Hf. destruct (Rle_dec (/ 2) (Re z)) as [Hh | Hh];
        [ | discriminate ].
      repeat split; assumption. }
  assert (H2 : INR (length L2) <= B).
  { assert (Hmap : (length (map refl1 L2) = length L2)%nat) by apply length_map.
    rewrite <- Hmap. apply Hbd.
    - apply NoDup_map_injective;
        [ intros x y HE; apply refl1_inj; exact HE
        | unfold L2; apply NoDup_filter; exact Hnd ].
    - intros z Hin. apply in_map_iff in Hin.
      destruct Hin as [w [Hwz Hw2]]; subst z.
      unfold L2 in Hw2. apply filter_In in Hw2.
      destruct Hw2 as [HinL Hf].
      destruct (Hz w HinL) as [Hz0 [Hr0 [Hr1 Hwin]]].
      unfold rhalf in Hf. destruct (Rle_dec (/ 2) (Re w)) as [Hh | Hh];
        [ discriminate | ].
      destruct (refl1_zero_in_strip w Hr0 Hr1 Hz0) as [Ha [Hb [Hc Hd]]].
      repeat split; try assumption.
      + rewrite Re_refl1. lra.
      + rewrite Hd. exact Hwin. }
  rewrite <- Hsplit, plus_INR. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  4.  the geometry: the window sits inside the count disk            *)
(*                                                                    *)
(*  centre 11/10 + i tj, count radius (9/20) * (37/20) = 333/400.      *)
(*  A zero with 1/2 <= Re < 1 and |Im - tj| <= 11/20 has               *)
(*    (Re - 11/10)^2 + (Im - tj)^2 <= 9/25 + 121/400 = 265/400         *)
(*  against the radius squared 110889/160000 = 0.693..., so it is      *)
(*  strictly inside with room to spare.                                *)
(* ----------------------------------------------------------------- *)

Definition cw (tj : R) : C := mkC (11 / 10) tj.

Lemma Cmod_lt_of_sq : forall (z : C) (r : R), 0 < r ->
  Re z * Re z + Im z * Im z < r * r -> Cmod z < r.
Proof.
  intros z r Hr H. unfold Cmod, Cnorm2.
  assert (Hs : sqrt (r * r) = r) by (apply sqrt_square; lra).
  rewrite <- Hs.
  apply sqrt_lt_1_alt. split; [ nra | exact H ].
Qed.

Lemma window_in_disk : forall tj z,
  / 2 <= Re z -> Re z < 1 -> Rabs (Im z - tj) <= 11 / 20 ->
  Cmod (Cminus z (cw tj)) < 333 / 400.
Proof.
  intros tj z H1 H2 H3.
  pose proof (Rabs_le_both _ _ H3) as [Hlo Hhi].
  apply Cmod_lt_of_sq; [ lra | ].
  assert (HR : Re (Cminus z (cw tj)) = Re z - 11 / 10)
    by (unfold cw, Cminus, Copp; cbn; ring).
  assert (HI : Im (Cminus z (cw tj)) = Im z - tj)
    by (unfold cw, Cminus, Copp; cbn; ring).
  rewrite HR, HI. nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  5.  the two analytic inputs at the centre 11/10 + i tj             *)
(* ----------------------------------------------------------------- *)

Lemma cw_mod_ub : forall tj, 0 <= tj -> Cmod (cw tj) <= tj + 11 / 10.
Proof.
  intros tj Ht. eapply Rle_trans; [ apply Cmod_le_sum | ].
  unfold cw; cbn [Re Im].
  rewrite (Rabs_pos_eq (11 / 10)) by lra.
  rewrite (Rabs_pos_eq tj) by lra. lra.
Qed.

Lemma cw_sub1_lb : forall tj, 0 <= tj -> tj <= Cmod (Cminus (cw tj) C1).
Proof.
  intros tj Ht.
  assert (HI : Im (Cminus (cw tj) C1) = tj)
    by (unfold cw, Cminus, Copp, C1; cbn; ring).
  pose proof (Cmod_Im_le (Cminus (cw tj) C1)) as H.
  rewrite HI, (Rabs_pos_eq tj) in H by lra. exact H.
Qed.

(* on the closed disk of radius 2 about the centre, Bfn1 is defined *)
Lemma disk_re_lb : forall tj s, 3 <= tj -> Cmod (Cminus s (cw tj)) <= 2 ->
  - 1 < Re s.
Proof.
  intros tj s Ht Hd.
  pose proof (Cmod_Re_le (Cminus s (cw tj))) as HR.
  assert (HE : Re (Cminus s (cw tj)) = Re s - 11 / 10)
    by (unfold cw, Cminus, Copp; cbn; ring).
  rewrite HE in HR.
  pose proof (Rabs_le_both _ _ (Rle_trans _ _ _ HR Hd)) as [Hlo Hhi]. lra.
Qed.

Lemma disk_ne1 : forall tj s, 3 <= tj -> Cmod (Cminus s (cw tj)) <= 2 ->
  Cminus C1 s <> C0.
Proof.
  intros tj s Ht Hd.
  assert (Hlb : 1 <= Cmod (Cminus s C1)).
  { pose proof (Cmod_rev (Cminus (cw tj) C1) (Cminus s C1)) as HT.
    replace (Cminus (Cminus (cw tj) C1) (Cminus s C1))
      with (Cminus (cw tj) s) in HT by ring.
    assert (HE : Cmod (Cminus (cw tj) s) = Cmod (Cminus s (cw tj)))
      by (replace (Cminus (cw tj) s) with (Copp (Cminus s (cw tj))) by ring;
          apply Cmod_opp').
    rewrite HE in HT.
    pose proof (Rabs_le_both _ _ HT) as [_ Hhi].
    pose proof (cw_sub1_lb tj ltac:(lra)). lra. }
  intro Hc.
  assert (Hz : Cminus s C1 = C0).
  { replace (Cminus s C1) with (Copp (Cminus C1 s)) by ring.
    rewrite Hc. apply Ceq; cbn; ring. }
  rewrite Hz, (proj2 (Cmod0 C0) eq_refl) in Hlb. lra.
Qed.

Definition Mcirc (tj : R) : R :=
  1 + (tj + 79 / 20) * (/ 2 + / 6 * ((tj + 59 / 20) * (tj + 79 / 20)) * 5).

Lemma Bfn1_circle_bound : forall tj u, 3 <= tj ->
  Cmod (Bfn1 (Cadd (cw tj) (arc (37 / 20) u))) <= Mcirc tj.
Proof.
  intros tj u Ht.
  set (s := Cadd (cw tj) (arc (37 / 20) u)).
  assert (Hd : Cmod (Cminus s (cw tj)) <= 2).
  { unfold s. replace (Cminus (Cadd (cw tj) (arc (37 / 20) u)) (cw tj))
      with (arc (37 / 20) u) by ring.
    rewrite (Cmod_arc (37 / 20) u ltac:(lra)). lra. }
  assert (Hre : - 1 < Re s) by (apply (disk_re_lb tj); assumption).
  assert (Hne : Cminus C1 s <> C0) by (apply (disk_ne1 tj); assumption).
  (* Re s is bounded below by -3/4 on the circle of radius 37/20 *)
  assert (Hre4 : - (3 / 4) <= Re s).
  { unfold s. assert (HE : Re (Cadd (cw tj) (arc (37 / 20) u))
                           = 11 / 10 + 37 / 20 * cos u)
      by (unfold cw, arc, Cadd; cbn; ring).
    rewrite HE. pose proof (COS_bound u) as [Hc1 Hc2]. lra. }
  assert (Hmod : Cmod s <= tj + 59 / 20).
  { unfold s. eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite (Cmod_arc (37 / 20) u ltac:(lra)).
    pose proof (cw_mod_ub tj ltac:(lra)). lra. }
  assert (Hmod1 : Cmod (Cadd s C1) <= tj + 79 / 20).
  { eapply Rle_trans; [ apply Cmod_triangle | ]. rewrite Cmod_one. lra. }
  assert (Hmodm1 : Cmod (Cminus s C1) <= tj + 79 / 20).
  { pose proof (Cmod_triangle s (Copp C1)) as HT.
    replace (Cadd s (Copp C1)) with (Cminus s C1) in HT by ring.
    assert (HC : Cmod (Copp C1) = 1) by (rewrite Cmod_opp'; apply Cmod_one).
    rewrite HC in HT. lra. }
  assert (HKh : Kh s <= / 6 * ((tj + 59 / 20) * (tj + 79 / 20))).
  { unfold Kh. pose proof (Cmod_nonneg s). pose proof (Cmod_nonneg (Cadd s C1)).
    nra. }
  assert (Hinv : 1 + / (Re s + 1) <= 5).
  { assert (H4 : / (Re s + 1) <= 4).
    { replace 4 with (/ (/ 4)) by field.
      apply Rinv_le_contravar; lra. }
    lra. }
  pose proof (Bfn1_bound s Hre Hne) as HB.
  pose proof (Cmod_nonneg (Cminus s C1)) as Hm0.
  pose proof (Kh_nonneg s) as HK0.
  assert (Hinvpos : 0 < / (Re s + 1)) by (apply Rinv_0_lt_compat; lra).
  assert (H1 : Kh s * (1 + / (Re s + 1))
               <= / 6 * ((tj + 59 / 20) * (tj + 79 / 20)) * 5)
    by (apply Rmult_le_compat; [ exact HK0 | lra | exact HKh | exact Hinv ]).
  assert (H2 : 0 <= / 2 + Kh s * (1 + / (Re s + 1))) by nra.
  assert (H3 : Cmod (Cminus s C1) * (/ 2 + Kh s * (1 + / (Re s + 1)))
               <= (tj + 79 / 20)
                  * (/ 2 + / 6 * ((tj + 59 / 20) * (tj + 79 / 20)) * 5))
    by (apply Rmult_le_compat; [ exact Hm0 | exact H2 | exact Hmodm1 | lra ]).
  unfold Mcirc. lra.
Qed.

(* the centre value, in logarithmic form -- no fourth root is ever taken *)
Definition Lcen (tj : R) : R :=
  ln tj + (- ln 1000 - ln (343 * (ln (2 * tj) + 10))) / 4.

Lemma cw_dom : forall tj, 3 <= tj ->
  0 < Re (cw tj) /\ Cminus C1 (cw tj) <> C0.
Proof.
  intros tj Ht. split; [ unfold cw; cbn; lra | ].
  apply (disk_ne1 tj); [ lra | ].
  replace (Cminus (cw tj) (cw tj)) with C0 by ring.
  rewrite (proj2 (Cmod0 C0) eq_refl). lra.
Qed.

Lemma zF_cw_pos : forall tj, 3 <= tj -> 0 < Cmod (zF (cw tj)).
Proof.
  intros tj Ht.
  pose proof (zeta_lower_log (11 / 10) tj ltac:(lra) ltac:(lra)
                ltac:(rewrite Rabs_pos_eq; lra)) as HZ.
  rewrite (Rabs_pos_eq tj) in HZ by lra.
  assert (Hcw : mkC (11 / 10) tj = cw tj) by reflexivity.
  rewrite Hcw in HZ.
  destruct (Cmod_nonneg (zF (cw tj))) as [Hp | He]; [ exact Hp | exfalso ].
  rewrite <- He in HZ.
  assert (H0 : (0:R) ^ 4 = 0) by ring. rewrite H0, Rmult_0_r in HZ. lra.
Qed.

Lemma Bfn1_centre_ne0 : forall tj, 3 <= tj -> Bfn1 (cw tj) <> C0.
Proof.
  intros tj Ht. destruct (cw_dom tj Ht) as [H0 H1].
  intro Hc. apply (proj1 (Bfn1_zero_iff (cw tj) H0 H1)) in Hc.
  pose proof (zF_cw_pos tj Ht) as Hp.
  rewrite Hc, (proj2 (Cmod0 C0) eq_refl) in Hp. lra.
Qed.

(* the centre value, bounded below LOGARITHMICALLY: zeta_lower_log is a
   fourth-power inequality, and taking logs avoids ever extracting a
   fourth root *)
Lemma Bfn1_centre_log_lb : forall tj, 3 <= tj ->
  Lcen tj <= ln (Cmod (Bfn1 (cw tj))).
Proof.
  intros tj Ht.
  destruct (cw_dom tj Ht) as [H0c H1c].
  set (Y := Cmod (zF (cw tj))).
  assert (HY : 0 < Y) by (apply zF_cw_pos; exact Ht).
  set (K := 343 * (ln (2 * tj) + 10)).
  assert (HlnK : 0 <= ln (2 * tj))
    by (rewrite <- ln_1; apply ln_mono_gen; lra).
  assert (HK : 0 < K) by (unfold K; lra).
  (* the fourth-power inequality *)
  pose proof (zeta_lower_log (11 / 10) tj ltac:(lra) ltac:(lra)
                ltac:(rewrite Rabs_pos_eq; lra)) as HZ.
  rewrite (Rabs_pos_eq tj) in HZ by lra.
  change (mkC (11 / 10) tj) with (cw tj) in HZ.
  fold Y in HZ. fold K in HZ.
  replace ((11 / 10 - 1) ^ 3) with (/ 1000) in HZ by (simpl; lra).
  (* logs *)
  assert (HY4 : 0 < Y ^ 4) by (apply pow_lt; exact HY).
  assert (Hln : ln (/ 1000) <= ln (K * Y ^ 4))
    by (apply ln_mono_gen; [ lra | exact HZ ]).
  rewrite ln_mult in Hln by lra.
  rewrite (ln_pow Y HY 4) in Hln.
  replace (INR 4) with 4 in Hln by (simpl; lra).
  rewrite ln_Rinv in Hln by lra.
  (* the modulus factors *)
  set (D := Cmod (Cminus (cw tj) C1)).
  assert (HD : tj <= D) by (unfold D; apply cw_sub1_lb; lra).
  assert (HDpos : 0 < D) by lra.
  assert (HBmod : Cmod (Bfn1 (cw tj)) = D * Y).
  { rewrite (Bfn1_eq (cw tj) H0c H1c), Cmod_mul.
    unfold D, Y. rewrite (zF_eq (cw tj) H0c H1c). reflexivity. }
  rewrite HBmod, ln_mult by lra.
  assert (HlnD : ln tj <= ln D) by (apply ln_mono_gen; lra).
  unfold Lcen. fold K. lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  6.  the window count                                              *)
(*                                                                    *)
(*  Peel parameters, all forced (see CPeelBoundGen's header):          *)
(*    alpha = 9/20   (1/4 is marginal: it would need Re s > -1.3)      *)
(*    lam = 1/53, Rr = 1961/20, so the bound circle has radius 37/20   *)
(*    R2 = 100, rh = 2   (Rr + 1 = 99.05 < 100; lam*(R2+1) = 101/53 < 2)*)
(*  giving count radius (9/20)*(37/20) = 333/400 and a bound circle    *)
(*  whose left edge is 11/10 - 37/20 = -3/4, inside Re s > -1.         *)
(* ----------------------------------------------------------------- *)

Definition Wbnd (tj : R) : R := (ln (2 * Mcirc tj) - Lcen tj) / ln (11 / 9).

Lemma Bfn1_ptcont_disk : forall tj z, 3 <= tj ->
  Cmod (Cminus z (cw tj)) < 2 -> ptcont_at Bfn1 z.
Proof.
  intros tj z Ht Hd eps Heps.
  destruct (Bfn1_holo z (disk_re_lb tj z Ht ltac:(lra))
              (disk_ne1 tj z Ht ltac:(lra))) as [d Hd'].
  destruct (is_Cderiv_cont Bfn1 z d Hd' eps Heps) as [del [Hdel HD]].
  exists del. split; [ exact Hdel | ]. intros z' Hz'.
  pose proof (HD (Cminus z' z) Hz') as H.
  replace (Cadd z (Cminus z' z)) with z' in H by ring. exact H.
Qed.

Lemma Mcirc_pos : forall tj, 3 <= tj -> 0 < Mcirc tj.
Proof. intros tj Ht. unfold Mcirc. nra. Qed.

Theorem zeta_window_halfcount : forall tj M, 3 <= tj -> NoDup M ->
  (forall z, In z M ->
     zF z = C0 /\ / 2 <= Re z /\ Re z < 1 /\ Rabs (Im z - tj) <= 11 / 20) ->
  INR (length M) <= Wbnd tj.
Proof.
  intros tj M Ht Hnd Hz.
  assert (Hrad : / 53 * (1961 / 20) = 37 / 20) by field.
  assert (Hcirc : forall u,
    Cmod (Bfn1 (Cadd (cw tj) (arc (/ 53 * (1961 / 20)) u))) <= Mcirc tj)
    by (intro u; rewrite Hrad; apply Bfn1_circle_bound; exact Ht).
  destruct (peel_count_at_centre (9 / 20) ltac:(lra) Bfn1 (cw tj)
              (/ 53) (1961 / 20) 100 2 (Mcirc tj)
              ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)
              (fun z Hz2 => Bfn1_holo z (disk_re_lb tj z Ht ltac:(lra))
                                        (disk_ne1 tj z Ht ltac:(lra)))
              (fun z Hz2 => Bfn1_ptcont_disk tj z Ht Hz2)
              (Bfn1_centre_ne0 tj Ht) Hcirc)
    as [l [Hl1 [Hl2 Hl3]]].
  (* M is contained in the peel list *)
  assert (Hincl : incl M l).
  { intros z HinM. destruct (Hz z HinM) as [Hz0 [Hr1 [Hr2 Hw]]].
    assert (H0 : 0 < Re z) by lra.
    assert (H1 : Cminus C1 z <> C0) by (apply strip_ne1; lra).
    apply Hl2.
    - rewrite Hrad.
      replace (9 / 20 * (37 / 20)) with (333 / 400) by field.
      apply (window_in_disk tj z); assumption.
    - apply (proj2 (Bfn1_zero_iff z H0 H1)). exact Hz0. }
  assert (Hlen : INR (length M) <= INR (length l))
    by (apply le_INR; apply (NoDup_incl_length Hnd Hincl)).
  (* the peel bound, rewritten *)
  assert (Hq : qpeel (9 / 20) = 11 / 9) by (unfold qpeel; field).
  rewrite Hq in Hl3.
  assert (Hlnq : 0 < ln (11 / 9))
    by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (HB : 0 < Cmod (Bfn1 (cw tj))).
  { destruct (Cmod_nonneg (Bfn1 (cw tj))) as [Hp | He]; [ exact Hp | ].
    exfalso. apply (Bfn1_centre_ne0 tj Ht).
    apply (proj1 (Cmod0 (Bfn1 (cw tj)))). lra. }
  assert (HM2 : 0 < 2 * Mcirc tj) by (pose proof (Mcirc_pos tj Ht); lra).
  assert (Hsplit : ln (2 * Mcirc tj / Cmod (Bfn1 (cw tj)))
                   = ln (2 * Mcirc tj) - ln (Cmod (Bfn1 (cw tj)))).
  { unfold Rdiv. rewrite ln_mult by (try lra; apply Rinv_0_lt_compat; lra).
    rewrite ln_Rinv by lra. ring. }
  rewrite Hsplit in Hl3.
  pose proof (Bfn1_centre_log_lb tj Ht) as Hlb.
  unfold Wbnd.
  apply Rle_trans with (INR (length l)); [ exact Hlen | ].
  eapply Rle_trans; [ exact Hl3 | ].
  apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; exact Hlnq | lra ].
Qed.

Theorem zeta_window_count : forall tj L, 3 <= tj -> NoDup L ->
  (forall z, In z L ->
     zF z = C0 /\ 0 < Re z /\ Re z < 1 /\ Rabs (Im z - tj) <= 11 / 20) ->
  INR (length L) <= 2 * Wbnd tj.
Proof.
  intros tj L Ht Hnd Hz.
  apply (halve_count_R tj (Wbnd tj) L Hnd Hz).
  intros M HndM HzM. apply zeta_window_halfcount; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  7.  non-vacuity                                                    *)
(*                                                                    *)
(*  A count theorem over an empty region typechecks and says nothing.  *)
(*  The first zero certified by NineZeros sits at 1/2 + 14.134...i;    *)
(*  it lies in the window at tj = 14 AND inside the count disk, with   *)
(*  Cmod = 0.614... against the radius 333/400 = 0.8325.               *)
(* ----------------------------------------------------------------- *)
Example first_zero_in_count_disk :
  Cmod (Cminus (mkC (/ 2) (1413 / 100)) (cw 14)) < 333 / 400.
Proof.
  apply (window_in_disk 14); cbn; try lra.
  rewrite Rabs_pos_eq; lra.
Qed.

Print Assumptions halve_count_R.
Print Assumptions window_in_disk.
Print Assumptions Bfn1_circle_bound.
Print Assumptions zeta_window_count.

(* ================================================================= *)
(*  END ZetaWindowCount.v                                             *)
(* ================================================================= *)
