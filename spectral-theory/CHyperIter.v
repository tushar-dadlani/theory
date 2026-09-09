(* ================================================================= *)
(*  CHyperIter.v  --  the Dirichlet convolution identity over C.      *)
(*                                                                    *)
(*  REDUNDANT.  CHyperbolaSwap.Chyperbola_swap is the same theorem,    *)
(*  already proved, in the Cls/seq indexing rather than CS/RS:         *)
(*    Cls (seq 1 N) (fun n => Cls (divisors n) (fun d => F d (n/d)))   *)
(*      = Cls (seq 1 N) (fun d => Cls (seq 1 (N/d)) (fun m => F d m))  *)
(*  and CDirichletProduct.cdirichlet_product already carries it all    *)
(*  the way to the infinite product with the tail estimate.  I did not *)
(*  check for those before writing this file.  Kept only because       *)
(*  hyper_iter_gen (the general-summand real form) is used by it and   *)
(*  is a genuine strengthening of HyperbolaSplit.hyper_iter; the C     *)
(*  half below duplicates existing work and nothing depends on it.     *)
(*                                                                    *)
(*    CS_{n<=X} CS_{d|n} a_d b_{n/d}  =  CS_{d<=X} a_d CS_{e<=X/d} b_e*)
(*                                                                    *)
(*  This is the ALGEBRAIC half of Dirichlet series multiplication --   *)
(*  the finite rearrangement, with no analysis in it.  Multiplying     *)
(*  sum Lambda(n) chi(n) n^{-s} by L(s,chi) convolves Lambda with 1,   *)
(*  and VonMangoldtReal.vonmangoldt_R says that convolution is ln, so  *)
(*  this identity is what turns the arithmetic into -L'/L.             *)
(*                                                                    *)
(*  IT IS OBTAINED FROM THE REAL ONE, NOT REPROVED.  The identity is a *)
(*  rearrangement of a finite sum, so it is linear in the summand;     *)
(*  Re and Im commute with every step.  Re (CS F X) = RS (Re o F) X    *)
(*  reduces the C statement to two instances of the R statement.       *)
(*                                                                    *)
(*  The one adjustment needed first: HyperbolaSplit.hyper_iter is      *)
(*  stated for a summand a_d * b_e, and Re (a_d * b_e) is not a        *)
(*  product but a difference of two.  So hyper_iter_gen restates it    *)
(*  for an ARBITRARY G d e -- which is also a shorter proof, since the *)
(*  RS_scal step that factored a_d out is no longer needed.            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ComplexField Cmodulus HyperbolaSplit.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- the real identity for a general summand.                 *)
(* ----------------------------------------------------------------- *)

Theorem hyper_iter_gen : forall (G : nat -> nat -> R) X,
  RS (fun n => RS (fun d => if (n mod d =? 0)%nat then G d (n / d)%nat else 0) X) X
  = RS (fun d => RS (fun e => G d e) (X / d)%nat) X.
Proof.
  intros G X. rewrite RS_swap. apply RS_ext. intros d Hd.
  rewrite (RS_indic_div (fun n => G d (n / d)%nat) d X ltac:(lia)).
  apply RS_ext. intros e He.
  replace (d * e / d)%nat with e; [ reflexivity | ].
  symmetry. replace (d * e)%nat with (e * d)%nat by lia. apply Nat.div_mul. lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- CS, the 1-indexed complex partial sum.                   *)
(* ----------------------------------------------------------------- *)

Fixpoint CS (F : nat -> C) (X : nat) : C :=
  match X with O => C0 | S X' => Cadd (CS F X') (F (S X')) end.

Lemma CS_Re : forall F X, Re (CS F X) = RS (fun n => Re (F n)) X.
Proof.
  intros F X. induction X as [| X IH]; [ reflexivity | ].
  replace (CS F (S X)) with (Cadd (CS F X) (F (S X))) by reflexivity.
  unfold Cadd; cbn [Re]. rewrite IH. reflexivity.
Qed.

Lemma CS_Im : forall F X, Im (CS F X) = RS (fun n => Im (F n)) X.
Proof.
  intros F X. induction X as [| X IH]; [ reflexivity | ].
  replace (CS F (S X)) with (Cadd (CS F X) (F (S X))) by reflexivity.
  unfold Cadd; cbn [Im]. rewrite IH. reflexivity.
Qed.

Lemma CS_ext : forall F G X,
  (forall n, (1 <= n <= X)%nat -> F n = G n) -> CS F X = CS G X.
Proof.
  intros F G X. induction X as [| X IH]; intro H; [ reflexivity | ].
  replace (CS F (S X)) with (Cadd (CS F X) (F (S X))) by reflexivity.
  replace (CS G (S X)) with (Cadd (CS G X) (G (S X))) by reflexivity.
  rewrite (H (S X)) by lia. f_equal. apply IH. intros n Hn. apply H. lia.
Qed.

Lemma CS_scal : forall c F X, CS (fun n => Cmul c (F n)) X = Cmul c (CS F X).
Proof.
  intros c F X. induction X as [| X IH].
  - cbn [CS]. apply Ceq; unfold Cmul, C0; cbn [Re Im]; ring.
  - replace (CS (fun n => Cmul c (F n)) (S X))
      with (Cadd (CS (fun n => Cmul c (F n)) X) (Cmul c (F (S X)))) by reflexivity.
    replace (CS F (S X)) with (Cadd (CS F X) (F (S X))) by reflexivity.
    rewrite IH. apply Ceq; unfold Cmul, Cadd; cbn [Re Im]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  Part C -- the complex identity.                                    *)
(* ----------------------------------------------------------------- *)

Theorem Chyper_iter_gen : forall (G : nat -> nat -> C) X,
  CS (fun n => CS (fun d => if (n mod d =? 0)%nat then G d (n / d)%nat else C0) X) X
  = CS (fun d => CS (fun e => G d e) (X / d)%nat) X.
Proof.
  intros G X. apply Ceq.
  - rewrite CS_Re, CS_Re.
    rewrite (RS_ext
      (fun n => Re (CS (fun d => if (n mod d =? 0)%nat then G d (n / d)%nat else C0) X))
      (fun n => RS (fun d => if (n mod d =? 0)%nat then Re (G d (n / d)%nat) else 0) X) X).
    2: { intros n _. rewrite CS_Re. apply RS_ext. intros d _.
         destruct (n mod d =? 0)%nat; [ reflexivity | unfold C0; reflexivity ]. }
    rewrite (RS_ext (fun d => Re (CS (fun e => G d e) (X / d)%nat))
                    (fun d => RS (fun e => Re (G d e)) (X / d)%nat) X)
      by (intros d _; apply CS_Re).
    apply (hyper_iter_gen (fun d e => Re (G d e)) X).
  - rewrite CS_Im, CS_Im.
    rewrite (RS_ext
      (fun n => Im (CS (fun d => if (n mod d =? 0)%nat then G d (n / d)%nat else C0) X))
      (fun n => RS (fun d => if (n mod d =? 0)%nat then Im (G d (n / d)%nat) else 0) X) X).
    2: { intros n _. rewrite CS_Im. apply RS_ext. intros d _.
         destruct (n mod d =? 0)%nat; [ reflexivity | unfold C0; reflexivity ]. }
    rewrite (RS_ext (fun d => Im (CS (fun e => G d e) (X / d)%nat))
                    (fun d => RS (fun e => Im (G d e)) (X / d)%nat) X)
      by (intros d _; apply CS_Im).
    apply (hyper_iter_gen (fun d e => Im (G d e)) X).
Qed.

Corollary Chyper_iter : forall (a b : nat -> C) X,
  CS (fun n => CS (fun d => if (n mod d =? 0)%nat
                            then Cmul (a d) (b (n / d)%nat) else C0) X) X
  = CS (fun d => Cmul (a d) (CS b (X / d)%nat)) X.
Proof.
  intros a b X.
  rewrite (Chyper_iter_gen (fun d e => Cmul (a d) (b e)) X).
  apply CS_ext. intros d _. apply CS_scal.
Qed.

Print Assumptions Chyper_iter.

(* ================================================================= *)
(*  END CHyperIter.v                                                  *)
(* ================================================================= *)
