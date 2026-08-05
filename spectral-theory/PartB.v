(* ================================================================= *)
(*  PartB.v  —  the defect sum is O(1), hence P' = 2 ln N + O(1)        *)
(*             (Step 2d, v3c assembly).                                 *)
(*                                                                    *)
(*  With bd1(m) = bdefect(m) (0 at m=1), BdW(y)=Sum_{m<=y} bd1(m),       *)
(*  A(y)=Sum_{d<=y} mu(d)/d, the symmetric hyperbola swap gives          *)
(*      Sum_{d<=N} (mu(d)/d) BdW(floor(N/d)) = Sum_{m<=N} bd1(m) A(floor(N/m)),*)
(*  bounded by 2*Sum|bd1| <= 2*32 = 64 (|A|<=2, Sum|b|<=32).            *)
(*  The Euler-Maclaurin identity  q(ln y) - W(y) = 2 - BdW(y)  then      *)
(*  gives, for P'(N) = Sum (mu(d)/d) q(ln floor(N/d)),                   *)
(*      P'(N) - W-sum = 2 Sum(mu/d) - Sum(mu/d) BdW(floor),             *)
(*  so with WsumEval (W-sum = 2 ln N + O(1)):  P'(N) = 2 ln N + O(1).    *)
(*  No Abel, no limits.  Axiom-clean.                                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import DirichletConv RealMobius SelbergSymmetry MertensVonMangoldt ChebyshevBound
        EulerMaclaurin MajorantSum MobiusMertens MobiusOverD SymHyperbola WsumEval.
Import ListNotations.
Open Scope R_scope.

Definition bd1 (m : nat) : R := if Nat.eqb m 1 then 0 else bdefect m.
Definition BdW (y : nat) : R := Rls (seq 1 y) bd1.
Definition Afun (y : nat) : R := Rls (seq 1 y) (fun d => IZR (mu d) / INR d).

Lemma abs_bnd : forall x c, Rabs x <= c -> - c <= x <= c.
Proof.
  intros x c H; pose proof (Rle_abs x); pose proof (Rle_abs (- x));
    rewrite Rabs_Ropp in *; lra.
Qed.

Lemma Rls_sub : forall (l : list nat) (f g : nat -> R),
  Rls l (fun x => f x - g x) = Rls l f - Rls l g.
Proof.
  intros l f g.
  rewrite (Rls_ext _ (fun x => f x - g x) (fun x => f x + (-1) * g x) l) by (intros; ring).
  rewrite Rls_add, <- Rls_scal; ring.
Qed.

Lemma Ginv_gfun_rec : forall y, Ginv gfun (S y) = Ginv gfun y + gfun (S y) / INR (S y).
Proof.
  intro y; unfold Ginv; rewrite seq_S, Rls_app, Rls_cons, Rls_nil2;
    replace (1 + y)%nat with (S y) by lia; ring.
Qed.

Lemma BdW_rec : forall y, BdW (S y) = BdW y + bd1 (S y).
Proof.
  intro y; unfold BdW; rewrite seq_S, Rls_app, Rls_cons, Rls_nil2;
    replace (1 + y)%nat with (S y) by lia; ring.
Qed.

Lemma bd1_abs_sum : forall N, Rls (seq 1 N) (fun m => Rabs (bd1 m)) <= 32.
Proof.
  destruct N as [|n'].
  - replace (seq 1 0) with (@nil nat) by reflexivity; rewrite Rls_nil2; lra.
  - change (seq 1 (S n')) with (1%nat :: seq 2 n'); rewrite Rls_cons.
    assert (Hb1 : bd1 1 = 0) by reflexivity.
    rewrite Hb1, Rabs_R0, Rplus_0_l.
    rewrite (Rls_ext _ (fun m => Rabs (bd1 m)) (fun m => Rabs (bdefect m)) (seq 2 n'))
      by (intros m Hm; apply in_seq in Hm; unfold bd1;
          destruct (Nat.eqb_spec m 1) as [Heq|Hne]; [ exfalso; lia | reflexivity ]).
    apply bdefect_sum_bound.
Qed.

(* the symmetric-swap identity for the defect sum *)
Lemma swap_BdW : forall N,
  Rls (seq 1 N) (fun d => IZR (mu d) / INR d * BdW (N / d)%nat)
  = Rls (seq 1 N) (fun m => bd1 m * Afun (N / m)%nat).
Proof.
  intro N.
  rewrite (Rls_ext _ (fun d => IZR (mu d) / INR d * BdW (N / d)%nat)
             (fun d => Rls (seq 1 (N / d)%nat) (fun m => IZR (mu d) / INR d * bd1 m))
             (seq 1 N)) by (intros d _; unfold BdW; rewrite Rls_scal; reflexivity).
  rewrite (hyperbola_swap_sym (fun d m => IZR (mu d) / INR d * bd1 m) N).
  apply Rls_ext; intros m _; unfold Afun.
  rewrite (Rls_ext _ (fun d => IZR (mu d) / INR d * bd1 m)
             (fun d => bd1 m * (IZR (mu d) / INR d)) (seq 1 (N / m)%nat)) by (intros; ring).
  rewrite <- Rls_scal; reflexivity.
Qed.

Lemma swap_bound : forall N,
  Rabs (Rls (seq 1 N) (fun d => IZR (mu d) / INR d * BdW (N / d)%nat)) <= 64.
Proof.
  intro N; rewrite (swap_BdW N).
  eapply Rle_trans; [ apply Rls_abs | ].
  eapply Rle_trans with (Rls (seq 1 N) (fun m => 2 * Rabs (bd1 m)));
    [ | rewrite <- Rls_scal; pose proof (bd1_abs_sum N); lra ].
  apply Rls_le; intros m Hm; apply in_seq in Hm.
  rewrite Rabs_mult.
  assert (HA : Rabs (Afun (N / m)%nat) <= 2).
  { destruct (Nat.eq_dec (N / m)%nat 0) as [Hz|Hz].
    - unfold Afun; rewrite Hz; replace (seq 1 0) with (@nil nat) by reflexivity;
        rewrite Rls_nil2, Rabs_R0; lra.
    - unfold Afun; apply mu_over_d_bound; lia. }
  pose proof (Rabs_pos (bd1 m)); nra.
Qed.

(* the Euler-Maclaurin identity  q(ln y) - W(y) = 2 - BdW(y) *)
Lemma psi_id : forall y, (1 <= y)%nat -> Qfun (INR y) - Ginv gfun y = 2 - BdW y.
Proof.
  induction y as [|y IH]; intro Hy; [ lia | ].
  destruct (Nat.eq_dec y 0) as [->|Hy0].
  - assert (HG : Ginv gfun 1 = -2).
    { unfold Ginv; replace (seq 1 1) with (1%nat :: nil) by reflexivity;
      rewrite Rls_cons, Rls_nil2; unfold gfun; rewrite INR_1, ln_1; field. }
    assert (HB : BdW 1 = 0).
    { unfold BdW; replace (seq 1 1) with (1%nat :: nil) by reflexivity;
      rewrite Rls_cons, Rls_nil2; assert (bd1 1 = 0) by reflexivity; lra. }
    assert (HQ : Qfun (INR 1) = 0) by (unfold Qfun; rewrite INR_1, ln_1; ring).
    rewrite HG, HB, HQ; lra.
  - specialize (IH ltac:(lia)).
    rewrite (Ginv_gfun_rec y), (BdW_rec y).
    assert (Hbd1 : bd1 (S y) = bdefect (S y)).
    { unfold bd1; destruct (Nat.eqb_spec (S y) 1) as [Heq|Hne]; [ lia | reflexivity ]. }
    rewrite Hbd1; unfold bdefect; replace (S y - 1)%nat with y by lia.
    assert (Hgh : gfun (S y) / INR (S y) = hfun (INR (S y))) by (unfold gfun, hfun; reflexivity).
    rewrite Hgh; lra.
Qed.

Definition Pprime (N : nat) : R :=
  Rls (seq 1 N) (fun d => IZR (mu d) / INR d * Qfun (INR (N / d)%nat)).

(* P'(N) = 2 ln N + O(1) *)
Theorem Pprime_bound : forall N, (1 <= N)%nat ->
  Rabs (Pprime N - 2 * ln (INR N)) <= 68 + (2 * Kup + 2).
Proof.
  intros N HN.
  set (W := Rls (seq 1 N) (fun d => IZR (mu d) / INR d * Ginv gfun (N / d)%nat)) in *.
  set (Amu := Rls (seq 1 N) (fun d => IZR (mu d) / INR d)) in *.
  set (Sw := Rls (seq 1 N) (fun d => IZR (mu d) / INR d * BdW (N / d)%nat)) in *.
  assert (Hkey : Pprime N - W = 2 * Amu - Sw).
  { unfold Pprime, W, Amu, Sw; rewrite <- Rls_sub.
    rewrite (Rls_ext _
               (fun d => IZR (mu d) / INR d * Qfun (INR (N / d)%nat)
                         - IZR (mu d) / INR d * Ginv gfun (N / d)%nat)
               (fun d => 2 * (IZR (mu d) / INR d)
                         - IZR (mu d) / INR d * BdW (N / d)%nat) (seq 1 N)).
    2:{ intros d Hd; apply in_seq in Hd.
        assert (Hdd : (d / d = 1)%nat) by (apply Nat.div_same; lia).
        assert (Hnd : (1 <= N / d)%nat) by (rewrite <- Hdd; apply Nat.Div0.div_le_mono; lia).
        pose proof (psi_id (N / d)%nat Hnd) as Hp.
        replace (2 * (IZR (mu d) / INR d) - IZR (mu d) / INR d * BdW (N / d)%nat)
          with (IZR (mu d) / INR d * (2 - BdW (N / d)%nat)) by ring.
        rewrite <- Hp; ring. }
    rewrite Rls_sub, <- Rls_scal; reflexivity. }
  pose proof (mu_over_d_bound N HN) as HAmu; fold Amu in HAmu.
  pose proof (swap_bound N) as Hsw; fold Sw in Hsw.
  pose proof (Wsum_bound N HN) as HW; fold W in HW.
  apply abs_bnd in HAmu; apply abs_bnd in Hsw; apply abs_bnd in HW.
  assert (HE : Pprime N - 2 * ln (INR N) = (2 * Amu - Sw) + (W - 2 * ln (INR N)))
    by (rewrite <- Hkey; ring).
  rewrite HE; apply Rabs_le; split; lra.
Qed.

Print Assumptions Pprime_bound.

(* ================================================================= *)
(*  END PartB.v  —  P'(N) = Sum (mu(d)/d) q(ln floor(N/d)) = 2 ln N+O(1).*)
(* ================================================================= *)
