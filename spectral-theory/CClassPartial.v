(* ================================================================= *)
(*  CClassPartial.v  --  the finite orthogonality identity, connecting *)
(*  the COMPLEX character sums to the REAL class sum.                  *)
(*                                                                    *)
(*    sum_{a<p-1} chi_a(m) * (partial sum of Lambda chi_a n^{-sig})    *)
(*      =  (p-1) * (partial sum of Lambda n^{-sig} over the class)     *)
(*                                                                    *)
(*  at every N, with no limits taken.  CharSelectorSeries proved the   *)
(*  same thing as a statement about limits; what the endgame needs is  *)
(*  the identity at each FIXED N, because CDirichletClass consumes a   *)
(*  lower bound on partial sums, and because at real sigma both sides  *)
(*  are real, so the whole thing lands in RtoC form.                   *)
(*                                                                    *)
(*  Everything is finite algebra: pull the constant chi_a(m) inside    *)
(*  the partial sum, swap the finite character sum with the partial    *)
(*  sum, and apply CharSelectorSeries.selector_pointwise term by term. *)
(*  The only new content is the bridge Ares_bridge, which says that at *)
(*  a REAL sigma the complex class term is RtoC of the real one --     *)
(*  that is where Cpw_RtoC turns n^{-s} into a real power.             *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CSeries CListSum CDirichlet
        CZetaTerm RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff CLSeries
        VonMangoldtGlobal CVonMangoldtChi CharSelectorSeries CDirichletClass
        CAbelTail LFunOne CPPowTail.
Import ListNotations.
Open Scope R_scope.

Lemma Cpsum_C0 : forall N, Cpsum (fun _ : nat => C0) N = C0.
Proof.
  induction N as [| N IH]; [ reflexivity | ].
  replace (Cpsum (fun _ : nat => C0) (S N))
    with (Cadd (Cpsum (fun _ : nat => C0) N) C0) by reflexivity.
  rewrite IH. ring.
Qed.

Lemma Cpsum_plus : forall F G N,
  Cpsum (fun k => Cadd (F k) (G k)) N = Cadd (Cpsum F N) (Cpsum G N).
Proof.
  intros F G N. induction N as [| N IH]; [ reflexivity | ].
  replace (Cpsum (fun k => Cadd (F k) (G k)) (S N))
    with (Cadd (Cpsum (fun k => Cadd (F k) (G k)) N) (Cadd (F (S N)) (G (S N))))
    by reflexivity.
  replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
  replace (Cpsum G (S N)) with (Cadd (Cpsum G N) (G (S N))) by reflexivity.
  rewrite IH. ring.
Qed.

Lemma Cpsum_scal_l : forall c F N,
  Cpsum (fun k => Cmul c (F k)) N = Cmul c (Cpsum F N).
Proof.
  intros c F N. induction N as [| N IH]; [ reflexivity | ].
  replace (Cpsum (fun k => Cmul c (F k)) (S N))
    with (Cadd (Cpsum (fun k => Cmul c (F k)) N) (Cmul c (F (S N)))) by reflexivity.
  replace (Cpsum F (S N)) with (Cadd (Cpsum F N) (F (S N))) by reflexivity.
  rewrite IH. ring.
Qed.

Lemma Cpsum_Csum_swap : forall (F : nat -> nat -> C) N M,
  Cpsum (fun k => Csum (fun a => F a k) M) N = Csum (fun a => Cpsum (F a) N) M.
Proof.
  intros F N M. induction M as [| M IH].
  - replace (Csum (fun a => Cpsum (F a) N) 0%nat) with C0 by reflexivity.
    rewrite (Cpsum_ext (fun k => Csum (fun a => F a k) 0%nat) (fun _ => C0) N)
      by (intro k; reflexivity).
    apply Cpsum_C0.
  - replace (Csum (fun a => Cpsum (F a) N) (S M))
      with (Cadd (Csum (fun a => Cpsum (F a) N) M) (Cpsum (F M) N)) by reflexivity.
    rewrite <- IH, <- Cpsum_plus.
    apply Cpsum_ext. intro k. reflexivity.
Qed.

Section CP.

Variable p g m : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.

Definition sc (sig : R) : C := mkC sig 0.

Lemma Ares_bridge : forall sig k,
  CharSelectorSeries.Ares p (sc sig) m (S k)
  = RtoC (CDirichletClass.Ares p m sig k).
Proof.
  intros sig k.
  unfold CharSelectorSeries.Ares, CDirichletClass.Ares, CDirichletClass.inclass, gC.
  replace (Copp (sc sig)) with (RtoC (- sig))
    by (apply Ceq; unfold Copp, RtoC, sc; cbn [Re Im]; ring).
  rewrite Cpw_RtoC.
  destruct (((S k) * m) mod p =? 1)%nat.
  - apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring.
  - apply Ceq; unfold C0, RtoC; cbn [Re Im]; ring.
Qed.

Theorem class_partial_identity : forall sig N,
  Csum (fun a => Cmul (dchar p g a m) (Cpsum (pchi p g a (sc sig)) N)) (p - 1)
  = RtoC (INR (p - 1) * sum_f_R0 (CDirichletClass.Ares p m sig) N).
Proof.
  intros sig N.
  rewrite (Csum_ext
             (fun a => Cmul (dchar p g a m) (Cpsum (pchi p g a (sc sig)) N))
             (fun a => Cpsum (fun k => Cmul (dchar p g a m)
                                (pchi p g a (sc sig) k)) N) (p - 1))
    by (intro a; symmetry; apply Cpsum_scal_l).
  rewrite <- Cpsum_Csum_swap.
  rewrite (Cpsum_ext
             (fun k => Csum (fun a => Cmul (dchar p g a m)
                                (pchi p g a (sc sig) k)) (p - 1))
             (fun k => Cmul (RtoC (INR (p - 1)))
                            (RtoC (CDirichletClass.Ares p m sig k))) N).
  - rewrite Cpsum_scal_l, Cpsum_RtoC.
    apply Ceq; unfold Cmul, RtoC; cbn [Re Im]; ring.
  - intro k.
    rewrite (Csum_ext
               (fun a => Cmul (dchar p g a m) (pchi p g a (sc sig) k))
               (fun a => Cmul (dchar p g a m) (achi p g a (sc sig) (S k))) (p - 1))
      by (intro a; rewrite achi_S; reflexivity).
    rewrite (selector_pointwise p g Hp Hg Hord (sc sig) m (S k)).
    rewrite Ares_bridge. reflexivity.
Qed.

End CP.

Print Assumptions class_partial_identity.

(* ================================================================= *)
(*  END CClassPartial.v                                               *)
(* ================================================================= *)
