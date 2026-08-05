(* ================================================================= *)
(*  MobiusOverD.v  —  | Sum_{d<=N} mu(d)/d | <= 2   (Step 2d, v2).      *)
(*                                                                    *)
(*  From the exact identity  Sum_{d<=N} mu(d) floor(N/d) = 1           *)
(*  (mu_hyperbola) and floor(N/d) = N/d - frac, frac in [0,1):         *)
(*      N * Sum(mu(d)/d) = 1 + Sum mu(d)*frac(d),                      *)
(*  and | Sum mu(d)*frac(d) | <= Sum |mu(d)|*frac(d) <= Sum 1 = N       *)
(*  (using |mu(d)| <= 1, MobiusBound, and frac < 1).  Hence            *)
(*      | Sum(mu(d)/d) | <= (1 + N)/N <= 2.                            *)
(*  This bounded partial sum is what kills the constant offset in the   *)
(*  Mobius-weighted evaluation of the summed Selberg formula.          *)
(*  Axiom-clean.                                                        *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List ZArith.
Require Import DirichletConv RealMobius SelbergSymmetry SelbergSum
        MertensVonMangoldt MobiusBound VonMangoldtGlobal.
Import ListNotations.
Open Scope R_scope.

Lemma Rls_nil2 : forall (f : nat -> R), Rls (@nil nat) f = 0.
Proof. reflexivity. Qed.

(* Rls is monotone *)
Lemma Rls_le : forall (l : list nat) (f g : nat -> R),
  (forall x, In x l -> f x <= g x) -> Rls l f <= Rls l g.
Proof.
  induction l as [|a l IH]; intros f g H; [ rewrite !Rls_nil2; lra | ].
  rewrite !Rls_cons; apply Rplus_le_compat.
  - apply H; left; reflexivity.
  - apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

(* Rls triangle inequality *)
Lemma Rls_abs : forall (l : list nat) (f : nat -> R),
  Rabs (Rls l f) <= Rls l (fun x => Rabs (f x)).
Proof.
  induction l as [|a l IH]; intros f; [ rewrite !Rls_nil2, Rabs_R0; lra | ].
  rewrite !Rls_cons; eapply Rle_trans; [ apply Rabs_triang | ].
  apply Rplus_le_compat; [ lra | apply IH ].
Qed.

Theorem mu_over_d_bound : forall N, (1 <= N)%nat ->
  Rabs (Rls (seq 1 N) (fun d => IZR (mu d) / INR d)) <= 2.
Proof.
  intros N HN.
  assert (H1 : 1 <= INR N) by (apply (le_INR 1); lia).
  set (S := Rls (seq 1 N) (fun d => IZR (mu d) / INR d)).
  (* N * S = 1 + fractional error *)
  assert (HNS : INR N * S
      = 1 + Rls (seq 1 N) (fun d => IZR (mu d) * (INR N / INR d - INR (N / d)%nat))).
  { unfold S; rewrite Rls_scal, <- (mu_hyperbola N HN),
      <- (Rls_add _ (fun d => IZR (mu d) * INR (N / d)%nat)
                    (fun d => IZR (mu d) * (INR N / INR d - INR (N / d)%nat)) (seq 1 N)).
    apply Rls_ext; intros d Hd; apply in_seq in Hd; field; apply not_0_INR; lia. }
  set (E := Rls (seq 1 N) (fun d => IZR (mu d) * (INR N / INR d - INR (N / d)%nat))) in HNS.
  (* |E| <= N *)
  assert (HE : Rabs E <= INR N).
  { unfold E; eapply Rle_trans; [ apply Rls_abs | ].
    eapply Rle_trans with (Rls (seq 1 N) (fun _ => 1));
      [ | rewrite Rls_seq_const; lra ].
    apply Rls_le; intros d Hd; apply in_seq in Hd.
    rewrite Rabs_mult.
    assert (Hmu : Rabs (IZR (mu d)) <= 1).
    { rewrite <- abs_IZR; replace 1 with (IZR 1) by (simpl; ring).
      apply IZR_le; destruct (mu_abs_le_1 d ltac:(lia)); lia. }
    pose proof (frac_bounds N d ltac:(lia)) as [Hf0 Hf1].
    assert (Hfr : Rabs (INR N / INR d - INR (N / d)%nat) <= 1)
      by (rewrite Rabs_pos_eq by lra; lra).
    pose proof (Rabs_pos (IZR (mu d))); nra. }
  (* conclude *)
  assert (Hfin : Rabs (INR N * S) <= 1 + INR N).
  { rewrite HNS; eapply Rle_trans; [ apply Rabs_triang | ]; rewrite Rabs_R1; lra. }
  rewrite Rabs_mult, (Rabs_pos_eq (INR N)) in Hfin by lra.
  pose proof (Rabs_pos S); nra.
Qed.

Print Assumptions mu_over_d_bound.

(* ================================================================= *)
(*  END MobiusOverD.v  —  | Sum_{d<=N} mu(d)/d | <= 2.                 *)
(* ================================================================= *)
