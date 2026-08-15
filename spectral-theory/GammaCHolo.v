(* ================================================================= *)
(*  GammaCHolo.v   (holomorphy of the complex Weierstrass factors)       *)
(*                                                                    *)
(*  Part of the GammaC != 0 program (Content C.3.2).  Using the newly     *)
(*  proven Cexpf derivative (CexpfDeriv.Cexpf_deriv), each Weierstrass    *)
(*  factor  wfac n w = (1 + w/n) e^{-w/n}  is holomorphic, hence so is    *)
(*  every finite partial product  Pprod (wcf w) N = prod_{k=1}^N wcf_k.   *)
(*                                                                    *)
(*     wfac_deriv       : each factor  (1+w/n)e^{-w/n}  has a derivative; *)
(*     Pprod_wcf_holo   : each finite partial product is holomorphic.     *)
(*                                                                    *)
(*  The remaining step to GammaC != 0 is the HOLOMORPHY OF THE INFINITE   *)
(*  LIMIT  Wc = lim Pprod  (a uniform-tail difference-quotient argument,  *)
(*  sum_deriv2-style), then GammaC.Wc = 1 via CWalk.reach.               *)
(*                                                                    *)
(*  Axioms: standard classical-Reals only (+ functional_extensionality). *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CexpFull CInfProd Holomorphic CDeriv
        CexpfDeriv GammaCWeierstrass.
Open Scope R_scope.

(* the abstract Weierstrass factor  (1 + w/n) e^{-w/n} *)
Definition wfac (n w : C) : C := Cmul (Cadd C1 (Cdiv w n)) (Cexpf (Copp (Cdiv w n))).

(* each factor is holomorphic (has a complex derivative), for every n, z *)
Theorem wfac_deriv : forall n z, { d : C | is_Cderiv (wfac n) z d }.
Proof.
  intros n z. set (c := Cinv n).
  assert (Hg : is_Cderiv (fun w => Cexpf (Copp (Cdiv w n))) z
                 (Cmul (Copp c) (Cexpf (Cadd (Cmul (Copp c) z) C0)))).
  { apply (is_Cderiv_ext (fun w => Cexpf (Cadd (Cmul (Copp c) w) C0))).
    - intro w. f_equal. unfold Cdiv; fold c. ring.
    - apply (Cderiv_comp_affine Cexpf (Copp c) C0 z
               (Cexpf (Cadd (Cmul (Copp c) z) C0))). apply Cexpf_deriv. }
  eexists. unfold wfac.
  apply (is_Cderiv_ext (fun w => Cmul (Cadd (Cmul c w) C1) (Cexpf (Copp (Cdiv w n))))).
  - intro w. f_equal. unfold Cdiv; fold c. ring.
  - apply (Cderiv_mul_affine c C1 (fun w => Cexpf (Copp (Cdiv w n))) z _ Hg).
Qed.

(* the product factor of GammaCWeierstrass matches wfac *)
Lemma wcf_wfac : forall w m, wcf w (S m) = wfac (RtoC (INR (S m))) w.
Proof. intros w m. reflexivity. Qed.

Lemma wcf_holo : forall m z, { d : C | is_Cderiv (fun w => wcf w (S m)) z d }.
Proof.
  intros m z. destruct (wfac_deriv (RtoC (INR (S m))) z) as [d Hd].
  exists d. apply (is_Cderiv_ext (wfac (RtoC (INR (S m))))); [ | exact Hd ].
  intro w. symmetry. apply wcf_wfac.
Qed.

(* every finite partial product prod_{k=1}^N wcf_k is holomorphic *)
Theorem Pprod_wcf_holo : forall N z, { d : C | is_Cderiv (fun w => Pprod (wcf w) N) z d }.
Proof.
  intros N z. induction N as [| N IH].
  - exists C0. apply (is_Cderiv_ext (fun _ => C1)); [ | apply Cderiv_const ].
    intro w. cbn [Pprod wcf]. reflexivity.
  - destruct IH as [dM HM]. destruct (wcf_holo N z) as [dS HS].
    eexists.
    apply (is_Cderiv_ext (fun w => Cmul (Pprod (wcf w) N) (wcf w (S N)))).
    + intro w. symmetry. apply Pprod_S.
    + apply (Cderiv_mul (fun w => Pprod (wcf w) N) (fun w => wcf w (S N)) z dM dS HM HS).
Qed.

Print Assumptions Pprod_wcf_holo.
