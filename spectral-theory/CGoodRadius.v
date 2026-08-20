(* ================================================================= *)
(*  CGoodRadius.v  —  a circle that misses a finite set of points.     *)
(*                                                                    *)
(*    good_radius_list : for every r > 0 and every finite list l of    *)
(*      complex numbers there is a radius rr in [2r, 4r] with          *)
(*                                                                    *)
(*        r / (length l + 1)  <=  |w - rho|                            *)
(*                                                                    *)
(*      for every rho in l and every w on the circle |w| = rr.         *)
(*                                                                    *)
(*  WHY THIS IS NEEDED.  The minimum modulus of the Hadamard product   *)
(*  cannot be estimated at an arbitrary point: near a zero the product *)
(*  is arbitrarily small, and the quotient xi/P -- though entire --    *)
(*  has no pointwise bound obtainable that way.  The classical repair  *)
(*  is to estimate on a circle chosen to keep away from the zeros and  *)
(*  then carry the bound inward by the Cauchy integral formula.  This  *)
(*  file produces the circle.                                         *)
(*                                                                    *)
(*  TWO THINGS MAKE IT CHEAP.                                         *)
(*                                                                    *)
(*  It is a ONE-DIMENSIONAL problem.  For |w| = rr the reverse         *)
(*  triangle inequality gives |w - rho| >= | rr - |rho| |, so the      *)
(*  circle never has to be reasoned about geometrically: it is enough  *)
(*  to place a REAL NUMBER away from the finite set of moduli.        *)
(*                                                                    *)
(*  The pigeonhole is done as an INDUCTION ON THE POINTS, not as a     *)
(*  counting argument.  Lay N+1 candidate radii across [2r, 4r],       *)
(*  spaced h apart.  Each point can spoil AT MOST ONE candidate --     *)
(*  two candidates within h/2 of the same point would be within h of   *)
(*  each other -- so removing the spoiled candidates for one point     *)
(*  drops the candidate list by at most one, and the induction never   *)
(*  runs out.  filter_drop_one is that step; NoDup is what stops a     *)
(*  repeated candidate being silently dropped twice.  Candidates are   *)
(*  indexed by nat, so NoDup comes free from seq_NoDup.                *)
(*                                                                    *)
(*  CPeelBound.prodfac_circle_lb gets a gap for free by demanding      *)
(*  every point sit inside Rr/4; that does not apply here, because the *)
(*  points of interest have modulus comparable to rr.  Hence the       *)
(*  pigeonhole.  Axiom-clean.                                          *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CSeries.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  two list lemmas                                                *)
(* ----------------------------------------------------------------- *)
Lemma filter_all : forall (A : Type) (p : A -> bool) (l : list A),
  (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  intros A p l H. induction l as [| x t IH]; [ reflexivity | ].
  cbn [filter]. rewrite (H x (or_introl eq_refl)).
  rewrite IH; [ reflexivity | intros y Hy; apply H; right; exact Hy ].
Qed.

(* filtering out the elements failing p removes at most one, provided at
   most one CAN fail and the list has no repeats *)
Lemma filter_drop_one : forall (A : Type) (p : A -> bool) (cs : list A),
  NoDup cs ->
  (forall c1 c2, In c1 cs -> In c2 cs -> p c1 = false -> p c2 = false -> c1 = c2) ->
  (length cs <= S (length (filter p cs)))%nat.
Proof.
  intros A p cs. induction cs as [| c t IH]; intros Hnd Huniq; [ cbn; lia | ].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hndt].
  assert (Huniqt : forall a b, In a t -> In b t -> p a = false -> p b = false -> a = b)
    by (intros a b Ha Hb Hpa Hpb;
        apply Huniq; [ right; exact Ha | right; exact Hb | exact Hpa | exact Hpb ]).
  destruct (p c) eqn:Hpc.
  - cbn [filter]. rewrite Hpc. cbn [length].
    pose proof (IH Hndt Huniqt). lia.
  - (* c is the only element that can fail p, so the tail is untouched *)
    assert (Hall : forall y, In y t -> p y = true).
    { intros y Hy. destruct (p y) eqn:Hpy; [ reflexivity | exfalso ].
      assert (Hyc : y = c)
        by (apply Huniq; [ right; exact Hy | left; reflexivity | exact Hpy | exact Hpc ]).
      apply Hnotin. rewrite <- Hyc. exact Hy. }
    cbn [filter]. rewrite Hpc, (filter_all A p t Hall). cbn [length]. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the pigeonhole                                                 *)
(* ----------------------------------------------------------------- *)
Lemma avoid_candidates : forall (c : nat -> R) (h : R), 0 < h ->
  (forall i j, i <> j -> h <= Rabs (c i - c j)) ->
  forall (l : list R) (cs : list nat),
    NoDup cs -> (length l < length cs)%nat ->
    exists j, In j cs /\ forall x, In x l -> h / 2 <= Rabs (x - c j).
Proof.
  intros c h Hh Hsep l. induction l as [| x t IH]; intros cs Hnd Hlen.
  - destruct cs as [| j cs']; [ cbn in Hlen; lia | ].
    exists j. split; [ left; reflexivity | intros y Hy; destruct Hy ].
  - set (p := fun j : nat => if Rlt_dec (Rabs (x - c j)) (h / 2) then false else true).
    (* at most one candidate is spoiled by x *)
    assert (Huniq : forall j k, In j cs -> In k cs -> p j = false -> p k = false -> j = k).
    { intros j k _ _ Hj Hk. unfold p in Hj, Hk.
      destruct (Rlt_dec (Rabs (x - c j)) (h / 2)) as [Hj' | _]; [ | discriminate ].
      destruct (Rlt_dec (Rabs (x - c k)) (h / 2)) as [Hk' | _]; [ | discriminate ].
      destruct (Nat.eq_dec j k) as [E | E]; [ exact E | exfalso ].
      pose proof (Hsep j k E) as Hs.
      assert (Htri : Rabs (c j - c k) <= Rabs (x - c j) + Rabs (x - c k)).
      { replace (c j - c k) with (- (x - c j) + (x - c k)) by ring.
        pose proof (Rabs_triang (- (x - c j)) (x - c k)) as HT.
        rewrite Rabs_Ropp in HT. lra. }
      lra. }
    pose proof (filter_drop_one nat p cs Hnd Huniq) as Hdrop.
    cbn [length] in Hlen.
    destruct (IH (filter p cs) ltac:(apply NoDup_filter; exact Hnd) ltac:(lia))
      as [j [Hjin Hjb]].
    destruct (proj1 (filter_In p j cs) Hjin) as [Hjcs Hpj].
    exists j. split; [ exact Hjcs | ].
    intros y Hy. destruct Hy as [Hy | Hy].
    + subst y. unfold p in Hpj.
      destruct (Rlt_dec (Rabs (x - c j)) (h / 2)) as [_ | Hge]; [ discriminate | lra ].
    + apply Hjb; exact Hy.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  an arithmetic progression is separated                         *)
(* ----------------------------------------------------------------- *)
Lemma INR_gap : forall i j : nat, i <> j -> 1 <= Rabs (INR i - INR j).
Proof.
  intros i j Hne.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]]; [ | contradiction | ].
  - assert (H : (S i <= j)%nat) by lia.
    pose proof (le_INR _ _ H) as HI. rewrite S_INR in HI.
    rewrite Rabs_left1 by lra. lra.
  - assert (H : (S j <= i)%nat) by lia.
    pose proof (le_INR _ _ H) as HI. rewrite S_INR in HI.
    rewrite Rabs_pos_eq by lra. lra.
Qed.

Lemma arith_sep : forall (a h : R), 0 < h ->
  forall i j : nat, i <> j -> h <= Rabs ((a + INR i * h) - (a + INR j * h)).
Proof.
  intros a h Hh i j Hne.
  replace (a + INR i * h - (a + INR j * h)) with ((INR i - INR j) * h) by ring.
  rewrite Rabs_mult, (Rabs_pos_eq h) by lra.
  pose proof (INR_gap i j Hne) as HG.
  pose proof (Rabs_pos (INR i - INR j)) as HP.
  nra.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  THE GOOD RADIUS                                                *)
(* ----------------------------------------------------------------- *)
Theorem good_radius_list : forall (r : R) (l : list C), 0 < r ->
  exists rr : R,
    2 * r <= rr /\ rr <= 4 * r /\
    forall rho, In rho l -> forall w, Cmod w = rr ->
      r / (INR (length l) + 1) <= Cmod (Cminus w rho).
Proof.
  intros r l Hr.
  set (N := length l).
  assert (HN0 : 0 <= INR N) by apply pos_INR.
  set (h := 2 * r / (INR N + 1)).
  assert (Hh : 0 < h) by (unfold h; apply Rdiv_lt_0_compat; lra).
  destruct (avoid_candidates (fun j : nat => 2 * r + INR j * h) h Hh
              (arith_sep (2 * r) h Hh) (map Cmod l) (seq 0 (S N))
              (seq_NoDup (S N) 0)
              ltac:(rewrite length_map, length_seq; unfold N; lia))
    as [j [Hjin Hjb]].
  assert (HjN : (j <= N)%nat)
    by (apply in_seq in Hjin; lia).
  assert (Hjn : INR j <= INR N) by (apply le_INR; exact HjN).
  assert (Hj0 : 0 <= INR j) by apply pos_INR.
  exists (2 * r + INR j * h).
  assert (HNh : INR N * h <= 2 * r).
  { unfold h. apply (Rmult_le_reg_r (INR N + 1)); [ lra | ].
    replace (INR N * (2 * r / (INR N + 1)) * (INR N + 1)) with (INR N * (2 * r))
      by (field; lra).
    nra. }
  assert (Hjh : INR j * h <= 2 * r)
    by (apply Rle_trans with (INR N * h); [ nra | exact HNh ]).
  split; [ nra | ]. split; [ nra | ].
  (* the distance bound *)
  assert (Hdel : r / (INR N + 1) = h / 2) by (unfold h; field; lra).
  intros rho Hrho w Hw.
  assert (Hmod : h / 2 <= Rabs (Cmod rho - (2 * r + INR j * h)))
    by (apply Hjb; apply in_map; exact Hrho).
  fold N. rewrite Hdel.
  apply Rle_trans with (Rabs (Cmod w - Cmod rho)); [ | apply Cmod_diff_le ].
  rewrite Hw, Rabs_minus_sym. exact Hmod.
Qed.

Print Assumptions good_radius_list.
