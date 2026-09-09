(* ================================================================= *)
(*  LambdaConv.v  --  the pointwise convolution (Lambda*G) * G = ln*G. *)
(*                                                                    *)
(*  For any COMPLETELY MULTIPLICATIVE G : nat -> C,                    *)
(*                                                                    *)
(*    sum_{d | n} (Lambda(d) G(d)) * G(n/d)  =  ln n * G(n)            *)
(*                                                                    *)
(*  Take G n = chi(n) n^{-s}.  Then the left side is the n-th          *)
(*  coefficient of the Dirichlet product of sum Lambda(m) chi(m) m^{-s}*)
(*  with L(s,chi), so CDirichletProduct.cdirichlet_product turns this  *)
(*  into                                                              *)
(*                                                                    *)
(*      Phi(s,chi) * L(s,chi)  =  sum_n chi(n) ln n  n^{-s}            *)
(*                                                                    *)
(*  and the right side is -L'(s,chi).  That is the log-derivative      *)
(*  identity, with no complex logarithm used anywhere.                 *)
(*                                                                    *)
(*  Stated in the Cls/divisors convention that cdirichlet_product      *)
(*  consumes, and it needs vonmangoldt_Rls -- the same identity as     *)
(*  VonMangoldtReal.vonmangoldt_R but in RealMobius.Rls form rather    *)
(*  than the RS-with-indicator form.                                   *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ComplexField Cmodulus CListSum RealMobius Totient
        DirichletVonMangoldt DirichletVonMangoldtGen VonMangoldtReal.
Import ListNotations.
Open Scope R_scope.

Lemma Rsl_Rls : forall (f : nat -> R) (l : list nat), Rsl f l = Rls l f.
Proof.
  intros f l. unfold Rsl, Rls.
  induction l as [| a l IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Theorem vonmangoldt_Rls : forall n, (1 <= n)%nat ->
  Rls (divisors n) Lam = ln (INR n).
Proof.
  intros n Hn. rewrite <- Rsl_Rls. unfold Lam.
  rewrite <- (ln_prodf vexp (divisors n)) by (intros d _; apply vexp_ge1).
  change (prodf (divisors n) vexp) with (vmprod n).
  rewrite (vonmangoldt n Hn). reflexivity.
Qed.

Lemma Cls_scal_r : forall (l : list nat) (f : nat -> R) (c : C),
  Cls l (fun d => Cmul (RtoC (f d)) c) = Cmul (RtoC (Rls l f)) c.
Proof.
  intros l f c. induction l as [| a l IH].
  - unfold Cls, Rls. simpl. apply Ceq; unfold Cmul, RtoC, C0; cbn [Re Im]; ring.
  - rewrite Cls_cons, IH, Rls_cons.
    apply Ceq; unfold Cmul, Cadd, RtoC; cbn [Re Im]; ring.
Qed.

Theorem lambda_conv : forall (G : nat -> C) n, (1 <= n)%nat ->
  (forall d e, (1 <= d)%nat -> (1 <= e)%nat -> G (d * e)%nat = Cmul (G d) (G e)) ->
  Cls (divisors n) (fun d => Cmul (Cmul (RtoC (Lam d)) (G d)) (G (n / d)%nat))
  = Cmul (RtoC (ln (INR n))) (G n).
Proof.
  intros G n Hn Hmul.
  rewrite <- (vonmangoldt_Rls n Hn), <- Cls_scal_r.
  apply Cls_ext. intros d Hd.
  unfold divisors in Hd. apply filter_In in Hd. destruct Hd as [Hseq Hmod].
  apply in_seq in Hseq.
  assert (Hd1 : (1 <= d)%nat) by lia.
  assert (Hm : (n mod d = 0)%nat) by (apply Nat.eqb_eq; exact Hmod).
  assert (Hsplit : (d * (n / d))%nat = n)
    by (pose proof (Nat.div_mod_eq n d); lia).
  assert (He1 : (1 <= n / d)%nat) by nia.
  replace (G n) with (Cmul (G d) (G (n / d)%nat)).
  2: { rewrite <- (Hmul d (n / d)%nat Hd1 He1). f_equal. exact Hsplit. }
  apply Ceq; unfold Cmul; cbn [Re Im]; ring.
Qed.

Print Assumptions vonmangoldt_Rls.
Print Assumptions lambda_conv.

(* ================================================================= *)
(*  END LambdaConv.v                                                  *)
(* ================================================================= *)
