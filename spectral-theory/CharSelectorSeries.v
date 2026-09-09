(* ================================================================= *)
(*  CharSelectorSeries.v  --  summing -L'/L over the characters.      *)
(*                                                                    *)
(*    sum_{a<p-1} chi_a(m) Phi(s,chi_a) = (p-1) sum_{n m = 1 mod p}   *)
(*                                              Lambda(n) n^{-s}      *)
(*                                                                    *)
(*  This is the algebraic core of Dirichlet's theorem: it takes the    *)
(*  log-derivative series, one per character, and combines them into a *)
(*  single series supported on ONE residue class.  Taking m to be the  *)
(*  inverse of r mod p makes n m = 1 mod p the condition n = r mod p.  *)
(*                                                                    *)
(*  Everything here is finite algebra plus one limit interchange.      *)
(*  The character sum collapses by CharOrthogonality.                  *)
(*  char_orthogonality_pair, and the interchange is legitimate because *)
(*  the sum over a is FINITE -- no rearrangement theorem is needed,    *)
(*  only CUn_cv_add iterated p-1 times (CUn_cv_Csum).                  *)
(*                                                                    *)
(*  What remains after this is purely analytic: as s -> 1+ the a = 0   *)
(*  term blows up (CLPrincipal, zeta's pole) while every other term    *)
(*  stays bounded (LFunOne), so the right-hand side diverges and the   *)
(*  residue class must contain infinitely many prime powers.           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List ZArith Znumtheory.
Require Import ComplexField Cmodulus CexpFull CSeries CListSum CDirichlet
        CZetaTerm RootsOfUnity ZmodOrder DirichletModP CTwistedCoeff
        VonMangoldtGlobal CVonMangoldtChi CVonMangoldtLChi CharOrthogonality.
Import ListNotations.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  Part A -- generic: finite sums commute with list sums and limits.  *)
(* ----------------------------------------------------------------- *)

Lemma Cls_add : forall (l : list nat) (f h : nat -> C),
  Cls l (fun x => Cadd (f x) (h x)) = Cadd (Cls l f) (Cls l h).
Proof.
  intros l f h. induction l as [| y l IH]; [ rewrite !Cls_nil; ring | ].
  rewrite !Cls_cons, IH. ring.
Qed.

Lemma Cls_C0 : forall (l : list nat), Cls l (fun _ => C0) = C0.
Proof.
  induction l as [| y l IH]; [ apply Cls_nil | ]. rewrite Cls_cons, IH. ring.
Qed.

Lemma Csum_scal_lr : forall K1 K2 F N,
  Csum (fun a => Cmul (Cmul K1 (F a)) K2) N = Cmul (Cmul K1 (Csum F N)) K2.
Proof.
  intros K1 K2 F N. induction N as [| N IH].
  - replace (Csum (fun a => Cmul (Cmul K1 (F a)) K2) 0%nat) with C0 by reflexivity.
    replace (Csum F 0%nat) with C0 by reflexivity. ring.
  - replace (Csum (fun a => Cmul (Cmul K1 (F a)) K2) (S N))
      with (Cadd (Csum (fun a => Cmul (Cmul K1 (F a)) K2) N)
                 (Cmul (Cmul K1 (F N)) K2)) by reflexivity.
    replace (Csum F (S N)) with (Cadd (Csum F N) (F N)) by reflexivity.
    rewrite IH. ring.
Qed.

Lemma Cls_Csum_swap : forall (F : nat -> nat -> C) (l : list nat) M,
  Cls l (fun n => Csum (fun a => F a n) M) = Csum (fun a => Cls l (F a)) M.
Proof.
  intros F l M. induction M as [| M IH].
  - replace (Csum (fun a => Cls l (F a)) 0%nat) with C0 by reflexivity.
    rewrite (Cls_ext nat (fun n => Csum (fun a => F a n) 0%nat) (fun _ => C0) l)
      by (intros x _; reflexivity).
    apply Cls_C0.
  - replace (Csum (fun a => Cls l (F a)) (S M))
      with (Cadd (Csum (fun a => Cls l (F a)) M) (Cls l (F M))) by reflexivity.
    rewrite <- IH.
    rewrite (Cls_ext nat (fun n => Csum (fun a => F a n) (S M))
               (fun n => Cadd (Csum (fun a => F a n) M) (F M n)) l)
      by (intros x _; reflexivity).
    apply Cls_add.
Qed.

Lemma CUn_cv_scal_l : forall u l c,
  CUn_cv u l -> CUn_cv (fun n => Cmul c (u n)) (Cmul c l).
Proof.
  intros u l c H eps He.
  destruct (Rle_lt_dec (Cmod c) 0) as [Hc | Hc].
  - assert (Hc0 : c = C0)
      by (apply (proj1 (Cmod0 c)); pose proof (Cmod_nonneg c); lra).
    exists 0%nat. intros n _. rewrite Hc0.
    replace (Cminus (Cmul C0 (u n)) (Cmul C0 l)) with C0 by ring.
    rewrite (proj2 (Cmod0 C0) eq_refl). exact He.
  - destruct (H (eps / Cmod c) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    exists N. intros n Hn.
    replace (Cminus (Cmul c (u n)) (Cmul c l)) with (Cmul c (Cminus (u n) l))
      by ring.
    rewrite Cmod_mul.
    apply Rlt_le_trans with (Cmod c * (eps / Cmod c)).
    + apply Rmult_lt_compat_l; [ lra | apply HN; exact Hn ].
    + apply Req_le. field. lra.
Qed.

Lemma CUn_cv_Csum : forall (u : nat -> nat -> C) (L : nat -> C) M,
  (forall a, CUn_cv (u a) (L a)) ->
  CUn_cv (fun N => Csum (fun a => u a N) M) (Csum L M).
Proof.
  intros u L M H. induction M as [| M IH].
  - intros eps He. exists 0%nat. intros n _.
    replace (Cminus (Csum (fun a => u a n) 0%nat) (Csum L 0%nat)) with C0
      by (replace (Csum (fun a => u a n) 0%nat) with C0 by reflexivity;
          replace (Csum L 0%nat) with C0 by reflexivity; ring).
    rewrite (proj2 (Cmod0 C0) eq_refl). exact He.
  - apply (CUn_cv_ext (fun N => Cadd (Csum (fun a => u a N) M) (u M N)));
      [ intro N; reflexivity | ].
    replace (Csum L (S M)) with (Cadd (Csum L M) (L M)) by reflexivity.
    apply CUn_cv_add; [ exact IH | apply H ].
Qed.

(* ----------------------------------------------------------------- *)
(*  Part B -- the selector.                                           *)
(* ----------------------------------------------------------------- *)

Section Selector.

Variable p g : nat.
Hypothesis Hp : prime (Z.of_nat p).
Hypothesis Hg : (1 <= g <= p - 1)%nat.
Hypothesis Hord : ord p g = (p - 1)%nat.
Variable s : C.
Hypothesis Hs : 1 < Re s.
Variable m : nat.

(* the von Mangoldt series restricted to the class  n m = 1 mod p *)
Definition Ares (n : nat) : C :=
  if ((n * m) mod p =? 1)%nat then Cmul (RtoC (Lam n)) (gC s (INR n)) else C0.

Lemma selector_pointwise : forall n,
  Csum (fun a => Cmul (dchar p g a m) (achi p g a s n)) (p - 1)
  = Cmul (RtoC (INR (p - 1))) (Ares n).
Proof.
  intro n. unfold Ares.
  rewrite (Csum_ext (fun a => Cmul (dchar p g a m) (achi p g a s n))
             (fun a => Cmul (Cmul (RtoC (Lam n))
                              (Cmul (dchar p g a n) (dchar p g a m)))
                            (gC s (INR n))) (p - 1)).
  2:{ intro a. unfold achi, Gchi, gC. ring. }
  rewrite Csum_scal_lr, (char_orthogonality_pair p g n m Hp Hg Hord).
  destruct ((n * m) mod p =? 1)%nat; ring.
Qed.

Theorem selector_identity :
  CUn_cv (fun N => Cls (seq 1 N) (fun n => Cmul (RtoC (INR (p - 1))) (Ares n)))
         (Csum (fun a => Cmul (dchar p g a m) (Phichi p g a Hg Hord s Hs)) (p - 1)).
Proof.
  apply (CUn_cv_ext (fun N => Csum (fun a =>
           Cmul (dchar p g a m) (Cls (seq 1 N) (achi p g a s))) (p - 1))).
  - intro N.
    rewrite (Csum_ext
               (fun a => Cmul (dchar p g a m) (Cls (seq 1 N) (achi p g a s)))
               (fun a => Cls (seq 1 N)
                  (fun n => Cmul (dchar p g a m) (achi p g a s n))) (p - 1))
      by (intro a; apply Cls_scal).
    rewrite <- Cls_Csum_swap.
    apply Cls_ext. intros n _. apply selector_pointwise.
  - apply CUn_cv_Csum. intro a.
    apply CUn_cv_scal_l. apply (achi_cv p g a Hg Hord s Hs).
Qed.

End Selector.

Print Assumptions selector_identity.

(* ================================================================= *)
(*  END CharSelectorSeries.v                                          *)
(* ================================================================= *)
