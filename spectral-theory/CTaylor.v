(* ================================================================= *)
(*  CTaylor.v  (identity-theorem plan, brick B3 — core)                *)
(*                                                                    *)
(*  The two reusable analytic ingredients of Taylor's theorem, in the  *)
(*  FINITE-remainder form (no infinite-series convergence needed):     *)
(*                                                                    *)
(*   1. kernel_geom : the finite geometric decomposition of the Cauchy *)
(*      kernel at the centre 0,                                        *)
(*        1/(z-w) = sum_{k<n} w^k/z^{k+1} + w^n/(z^n (z-w)),           *)
(*      pure C-field algebra (proved by induction, via `field`).       *)
(*                                                                    *)
(*   2. Cintf_Csum : term-by-term integration of a FINITE sum over a   *)
(*      contour,  oint (sum_{k<n} g_k) = sum_{k<n} oint g_k            *)
(*      (induction on n via Cintf_add) -- the "term-by-term" swap the   *)
(*      plan flagged, but finite, so elementary.                       *)
(*                                                                    *)
(*  Together with the ML estimate on the remainder integral these give *)
(*  Taylor-with-remainder and (B4) all-coefficients-zero => f == 0.     *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only.                            *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral
        CGoursatLin CWinding CDeriv RootsOfUnity.
Open Scope R_scope.

(* ---- C1 <> C0, and powers of a nonzero base are nonzero ---- *)
Lemma C1_ne0 : C1 <> C0.
Proof. intro H; apply (f_equal Re) in H; cbn in H; lra. Qed.

Lemma Cpow_ne0 : forall z n, z <> C0 -> Cpow z n <> C0.
Proof.
  intros z n Hz; induction n as [|n IH]; cbn [Cpow].
  - exact C1_ne0.
  - apply Cmul_ne0; [ exact Hz | exact IH ].
Qed.

(* ================================================================= *)
(*  1.  The geometric kernel identity  (centre 0)                     *)
(* ================================================================= *)

Definition tterm (w z : C) (k : nat) : C := Cmul (Cpow w k) (Cinv (Cpow z (S k))).
Definition trem  (w z : C) (n : nat) : C :=
  Cmul (Cpow w n) (Cinv (Cmul (Cpow z n) (Cminus z w))).

Lemma kernel_geom : forall w z n, z <> C0 -> Cminus z w <> C0 ->
  Cinv (Cminus z w) = Cadd (Csum (tterm w z) n) (trem w z n).
Proof.
  intros w z n Hz Hzw. induction n as [|n IH].
  - cbn [Csum]. unfold trem. cbn [Cpow].
    replace (Cmul C1 (Cminus z w)) with (Cminus z w) by ring. ring.
  - rewrite IH. cbn [Csum].
    assert (Hstep : trem w z n = Cadd (tterm w z n) (trem w z (S n))).
    { unfold trem, tterm. cbn [Cpow].
      set (P := Cpow z n) in *. set (Q := Cpow w n) in *.
      assert (HP : P <> C0) by (apply Cpow_ne0; exact Hz).
      field. repeat split; assumption. }
    rewrite Hstep. ring.
Qed.

(* ================================================================= *)
(*  2.  Term-by-term integration of a finite sum over a contour       *)
(* ================================================================= *)

Lemma Ccont_Csum : forall (h : nat -> R -> C),
  (forall k, Ccont (h k)) ->
  forall n, Ccont (fun u => Csum (fun k => h k u) n).
Proof.
  intros h Hh n; induction n as [|n IH]; cbn [Csum].
  - apply Ccont_const.
  - apply Ccont_add; [ exact IH | apply Hh ].
Qed.

Lemma Cintf_Csum : forall (h : nat -> R -> C) (n : nat)
  (Hh : forall k, Ccont (h k))
  (Hsum : Ccont (fun u => Csum (fun k => h k u) n)) a b, a <= b ->
  Cintf (fun u => Csum (fun k => h k u) n) Hsum a b
  = Csum (fun k => Cintf (h k) (Hh k) a b) n.
Proof.
  intros h n Hh; induction n as [|n IH]; intros Hsum a b Hab.
  - cbn [Csum]. rewrite (Cintf_const_ab C0 Hsum a b). ring.
  - cbn [Csum].
    rewrite (Cintf_add (fun u => Csum (fun k => h k u) n) (h n)
               (Ccont_Csum h Hh n) (Hh n) Hsum a b Hab).
    rewrite (IH (Ccont_Csum h Hh n) a b Hab). reflexivity.
Qed.

Print Assumptions kernel_geom.
Print Assumptions Cintf_Csum.
