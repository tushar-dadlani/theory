(* ================================================================= *)
(*  CAbelSummation.v  —  C-valued summation by parts.                   *)
(*                                                                    *)
(*  The real AbelSummation only handles real factors; the von Mangoldt  *)
(*  series Sum Lam(n) n^{-s} pairs a real coefficient a_k with a complex *)
(*  weight c_k = k^{-s}.  Cabel_summation is the exact C-valued mirror   *)
(*  (same telescoping induction), the discrete half of the integral      *)
(*  representation Phi(s) = s Int_1^oo psi(floor x) x^{-s-1} dx.         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField CSeries.
Open Scope R_scope.

Theorem Cabel_summation : forall (a c : nat -> C) (M : nat),
  Cpsum (fun k => Cmul (a k) (c k)) (S M)
  = Cminus (Cmul (Cpsum a (S M)) (c (S M)))
           (Cpsum (fun k => Cmul (Cpsum a k) (Cminus (c (S k)) (c k))) M).
Proof.
  intros a c M; induction M as [|M IH].
  - cbn [Cpsum]; ring.
  - change (Cpsum (fun k => Cmul (a k) (c k)) (S (S M)))
      with (Cadd (Cpsum (fun k => Cmul (a k) (c k)) (S M))
                 (Cmul (a (S (S M))) (c (S (S M))))).
    change (Cpsum a (S (S M)))
      with (Cadd (Cpsum a (S M)) (a (S (S M)))).
    change (Cpsum (fun k => Cmul (Cpsum a k) (Cminus (c (S k)) (c k))) (S M))
      with (Cadd (Cpsum (fun k => Cmul (Cpsum a k) (Cminus (c (S k)) (c k))) M)
                 (Cmul (Cpsum a (S M)) (Cminus (c (S (S M))) (c (S M))))).
    rewrite IH; ring.
Qed.

Definition Cabel_correction (a c : nat -> C) (M : nat) : C :=
  Cpsum (fun k => Cmul (Cpsum a k) (Cminus (c (S k)) (c k))) M.

Corollary Cabel_summation' : forall (a c : nat -> C) (M : nat),
  Cpsum (fun k => Cmul (a k) (c k)) (S M)
  = Cminus (Cmul (Cpsum a (S M)) (c (S M))) (Cabel_correction a c M).
Proof. intros a c M; unfold Cabel_correction; apply Cabel_summation. Qed.

Print Assumptions Cabel_summation.

(* ================================================================= *)
(*  END CAbelSummation.v  —  C-valued summation by parts.               *)
(* ================================================================= *)
