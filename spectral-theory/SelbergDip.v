(* ================================================================= *)
(*  SelbergDip.v  —  RUNG 3c-A':  dip_scales L -> avg_below L.         *)
(*                                                                    *)
(*  avg_below L needs the Lambda-weighted average                      *)
(*    Sum_{d<=N} (Lam d / d) Vrem(N/d)  <=  (L - rho) ln N + C0        *)
(*  with rho > 0.  Since every Vrem(N/d) <= L + eps (limsup), the ONLY  *)
(*  way to beat L is a positive-Lambda-weight set of DIP scales where   *)
(*  Vrem(N/d) <= b < L.  This file proves that IS sufficient:           *)
(*                                                                    *)
(*    dip_avg_below : is_limsup Vrem L -> dip_scales L -> avg_below L.  *)
(*                                                                    *)
(*  Proof: split seq 1 N at q = N/N0 into bulk (d<=q, so N/d>=N0, so    *)
(*  Vrem(N/d) < L+eps, minus the dip credit) and tail (d>q, Vrem<=Kup-1, *)
(*  Lambda-weight O(1) by mertens_tail).  The dip credit (L+eps-b)*theta *)
(*  ln N beats eps, giving rho = (L-b) theta / 2 > 0.  Axiom-clean.     *)
(*  This isolates the wall to the single density fact dip_scales.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound ChebyshevPrime VonMangoldtGlobal
        RealMobius MobiusOverD SelbergEndgame SelbergAverage PsiAsymp
        LimSup SelbergCollapse MertensVonMangoldt MertensTail SmoothingLemma.
Open Scope R_scope.

(* ---- small real/nat helpers ---- *)
Lemma Rls_add' : forall (l : list nat) (f g : nat -> R),
  Rls l (fun k => f k + g k) = Rls l f + Rls l g.
Proof.
  induction l as [|a l IH]; intros f g;
    [ rewrite !Rls_nil2; ring | rewrite !Rls_cons, IH; ring ].
Qed.

Lemma Rls_lin : forall (l : list nat) (c1 c2 : R) (u v : nat -> R),
  Rls l (fun d => c1 * u d + c2 * v d) = c1 * Rls l u + c2 * Rls l v.
Proof.
  induction l as [|a l IH]; intros c1 c2 u v;
    [ rewrite !Rls_nil2; ring | rewrite !Rls_cons, IH; ring ].
Qed.

Lemma Rls_scal' : forall (l : list nat) (c : R) (u : nat -> R),
  Rls l (fun d => c * u d) = c * Rls l u.
Proof.
  induction l as [|a l IH]; intros c u;
    [ rewrite !Rls_nil2; ring | rewrite !Rls_cons, IH; ring ].
Qed.

Lemma ln_le' : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy; destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq];
    [ left; apply ln_increasing; assumption | rewrite Heq; lra ].
Qed.

Lemma Ndiv_ge : forall N N0 d, (1 <= N0)%nat -> (1 <= d)%nat ->
  (d <= N / N0)%nat -> (N0 <= N / d)%nat.
Proof.
  intros N N0 d HN0 Hd Hle.
  assert (Hmd : (N0 * (N / N0) <= N)%nat) by apply Nat.Div0.mul_div_le.
  apply Nat.div_le_lower_bound; [ lia | nia ].
Qed.

Lemma tail_ln : forall N N0, (1 <= N0)%nat -> (2 * N0 <= N)%nat ->
  ln (INR N) - ln (INR (N / N0)%nat) <= ln (2 * INR N0).
Proof.
  intros N N0 HN0 HN.
  assert (Hq1 : (1 <= N / N0)%nat) by (apply Nat.div_le_lower_bound; lia).
  assert (HqR : 0 < INR (N / N0)%nat) by (apply lt_0_INR; lia).
  assert (Hn0R : 0 < INR N0) by (apply lt_0_INR; lia).
  assert (HnR : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hnat : (N <= 2 * (N0 * (N / N0)))%nat).
  { pose proof (Nat.div_mod N N0 ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound N N0 ltac:(lia)) as Hmod. lia. }
  assert (Heq : INR (2 * (N0 * (N / N0)))%nat = 2 * INR N0 * INR (N / N0)%nat)
    by (rewrite !mult_INR; simpl; ring).
  assert (Hstep : ln (INR N) <= ln (2 * INR N0) + ln (INR (N / N0)%nat)).
  { rewrite <- ln_mult by lra.
    apply ln_le'; [ exact HnR | ].
    apply Rle_trans with (INR (2 * (N0 * (N / N0)))%nat);
      [ apply le_INR; exact Hnat | rewrite Heq; apply Req_le; ring ]. }
  lra.
Qed.

(* ---- the DIP hypothesis ---- *)
Definition ind_dip (b : R) (N d : nat) : R :=
  if Rle_dec (Vrem (N / d)%nat) b then 1 else 0.

Definition dipw (b : R) (N : nat) : R :=
  Rls (seq 1 N) (fun d => Lam d / INR d * ind_dip b N d).

Definition dip_scales (L : R) : Prop :=
  exists b theta, b < L /\ 0 < theta /\
    exists K, forall N, (K <= N)%nat -> theta * ln (INR N) <= dipw b N.

(* ---- THE REDUCTION ---- *)
Theorem dip_avg_below : forall L, is_limsup Vrem L -> dip_scales L -> avg_below L.
Proof.
  intros L Hlim Hdip.
  assert (HL0 : 0 <= L)
    by (apply (is_limsup_nonneg Vrem L Hlim); intros; apply Vrem_nonneg).
  destruct Hdip as [b [theta [Hbl [Htheta [Kdip Hdw]]]]].
  destruct Hlim as [Hub _].
  assert (Heps : 0 < (L - b) * theta / 2) by nra.
  destruct (Hub ((L - b) * theta / 2) Heps) as [N0' HN0'].
  set (N0 := Nat.max N0' 2).
  assert (HN0lo : (2 <= N0)%nat) by (unfold N0; lia).
  assert (HN0'2 : forall n, (N0 <= n)%nat -> Vrem n < L + (L - b) * theta / 2)
    by (intros n Hn; apply HN0'; unfold N0 in Hn; lia).
  set (Ctail := ln (2 * INR N0) + 2 * Kup).
  exists ((L - b) * theta / 2),
         ((L + (L - b) * theta / 2) * Kup
          + (L + (L - b) * theta / 2 - b) * Ctail + (Kup - 1) * Ctail).
  split; [ nra | ].
  exists (Nat.max (Nat.max Kdip (2 * N0)) 2).
  intros N HN.
  assert (HNge2 : (2 <= N)%nat) by lia.
  assert (HN2N0 : (2 * N0 <= N)%nat) by lia.
  assert (HNKdip : (Kdip <= N)%nat) by lia.
  set (q := (N / N0)%nat).
  assert (Hq1 : (1 <= q)%nat) by (unfold q; apply Nat.div_le_lower_bound; lia).
  assert (HqN : (q <= N)%nat)
    by (unfold q; pose proof (Nat.Div0.mul_div_le N N0) as Hm; nia).
  assert (HlnN : 0 < ln (INR N)) by (apply ln_INR_pos; lia).
  set (A := L + (L - b) * theta / 2).
  assert (HAval : A = L + (L - b) * theta / 2) by reflexivity.
  assert (HA : 0 <= A) by (rewrite HAval; nra).
  assert (HAb : 0 <= A - b) by (rewrite HAval; nra).
  assert (Hln2 : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (HKupm : 0 <= Kup - 1) by (unfold Kup; lra).
  (* seq split *)
  assert (Hseq : seq 1 N = seq 1 q ++ seq (S q) (N - q)).
  { replace N with (q + (N - q))%nat at 1 by lia.
    rewrite List.seq_app; f_equal; f_equal; lia. }
  set (g := fun d => Lam d / INR d).
  assert (Hgnn : forall d, (1 <= d)%nat -> 0 <= g d).
  { intros d Hd; unfold g, Rdiv; apply Rmult_le_pos;
      [ apply Lam_nonneg | left; apply Rinv_0_lt_compat; apply lt_0_INR; lia ]. }
  (* tail Lambda-weight = msum N - msum q *)
  assert (Htail_sum : Rls (seq (S q) (N - q)) g = msum N - msum q).
  { unfold g; rewrite (msum_Rls N), (msum_Rls q), Hseq, Rls_app; ring. }
  set (Dq := Rls (seq 1 q) (fun d => Lam d / INR d * ind_dip b N d)).
  (* BULK *)
  assert (Hbulk : Rls (seq 1 q) (fun d => Lam d / INR d * Vrem (N / d)%nat)
                  <= A * msum q - (A - b) * Dq).
  { apply Rle_trans with (Rls (seq 1 q)
      (fun d => A * (Lam d / INR d) + (- (A - b)) * (Lam d / INR d * ind_dip b N d))).
    - apply Rls_le; intros d Hd; apply in_seq in Hd.
      replace (A * (Lam d / INR d) + (- (A - b)) * (Lam d / INR d * ind_dip b N d))
        with (Lam d / INR d * (A - (A - b) * ind_dip b N d)) by ring.
      apply Rmult_le_compat_l; [ apply Hgnn; lia | ].
      unfold ind_dip; destruct (Rle_dec (Vrem (N / d)%nat) b) as [Hd1 | Hd0].
      + lra.
      + replace (A - (A - b) * 0) with A by ring.
        unfold A; apply Rlt_le, HN0'2, Ndiv_ge; unfold q in *; lia.
    - rewrite (Rls_lin (seq 1 q) A (- (A - b))).
      rewrite <- (msum_Rls q); fold Dq; lra. }
  (* TAIL *)
  assert (Htail : Rls (seq (S q) (N - q)) (fun d => Lam d / INR d * Vrem (N / d)%nat)
                  <= (Kup - 1) * (msum N - msum q)).
  { apply Rle_trans with (Rls (seq (S q) (N - q)) (fun d => (Kup - 1) * (Lam d / INR d))).
    - apply Rls_le; intros d Hd; apply in_seq in Hd.
      apply Rle_trans with (Lam d / INR d * (Kup - 1));
        [ apply Rmult_le_compat_l; [ apply Hgnn; lia | apply Vrem_bound_all ]
        | apply Req_le; ring ].
    - rewrite (Rls_scal' (seq (S q) (N - q)) (Kup - 1)).
      fold g; rewrite Htail_sum; lra. }
  (* DIP decomposition *)
  assert (Htail_dip : Rls (seq (S q) (N - q)) (fun d => Lam d / INR d * ind_dip b N d)
                      <= msum N - msum q).
  { rewrite <- Htail_sum; apply Rls_le; intros d Hd; apply in_seq in Hd.
    unfold g, ind_dip; destruct (Rle_dec (Vrem (N / d)%nat) b);
      [ rewrite Rmult_1_r; lra | rewrite Rmult_0_r; apply Hgnn; lia ]. }
  assert (Hdipw_split : dipw b N = Dq + Rls (seq (S q) (N - q)) (fun d => Lam d / INR d * ind_dip b N d)).
  { unfold dipw, Dq; rewrite Hseq, Rls_app; reflexivity. }
  pose proof (Hdw N HNKdip) as Hdwn.
  assert (HDq : theta * ln (INR N) - (msum N - msum q) <= Dq) by lra.
  (* msum q <= ln N + Kup *)
  assert (Hmsq : msum q <= ln (INR N) + Kup).
  { pose proof (mertens_lam q ltac:(lia)) as Hml.
    pose proof (Rle_abs (msum q - ln (INR q))) as Hab.
    assert (Hlnq : ln (INR q) <= ln (INR N))
      by (apply ln_le'; [ apply lt_0_INR; lia | apply le_INR; lia ]).
    lra. }
  (* tail weight bound *)
  assert (Htail_bd : msum N - msum q <= Ctail).
  { pose proof (mertens_tail q N ltac:(lia) ltac:(lia)) as Hmt.
    pose proof (tail_ln N N0 ltac:(lia) HN2N0) as Htl.
    unfold Ctail, q in *; lra. }
  (* assemble *)
  assert (Hbulk2 : Rls (seq 1 q) (fun d => Lam d / INR d * Vrem (N / d)%nat)
                   <= A * (ln (INR N) + Kup) - (A - b) * (theta * ln (INR N) - (msum N - msum q))).
  { nra. }
  assert (HK1 : A - (A - b) * theta <= L - (L - b) * theta / 2) by (rewrite HAval; nra).
  assert (Hkey : (A - (A - b) * theta) * ln (INR N)
                 <= (L - (L - b) * theta / 2) * ln (INR N))
    by (apply Rmult_le_compat_r; [ lra | exact HK1 ]).
  rewrite Hseq, Rls_app.
  assert (Hcomb : Rls (seq 1 q) (fun d => Lam d / INR d * Vrem (N / d)%nat)
                  + Rls (seq (S q) (N - q)) (fun d => Lam d / INR d * Vrem (N / d)%nat)
                  <= (A - (A - b) * theta) * ln (INR N)
                     + (A * Kup + (A - b) * Ctail + (Kup - 1) * Ctail)) by nra.
  lra.
Qed.

Print Assumptions dip_avg_below.

(* ================================================================= *)
(*  END SelbergDip.v  —  the wall is now isolated to dip_scales, the    *)
(*  positive-Lambda-weight density of scales where Vrem dips below its  *)
(*  own limsup (the Erdos-Selberg sign-balancing crux).                *)
(* ================================================================= *)
