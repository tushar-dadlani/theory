(* ================================================================= *)
(*  ZetaInvHolo.v  —  Milestone B, brick B3: 1/zeta holomorphic, and    *)
(*  zeta non-vanishing on an OPEN neighborhood of the line Re s = 1.     *)
(*                                                                    *)
(*  Using zF (the total zeta function, B2) and its holomorphy, the       *)
(*  reciprocal 1/zF is holomorphic wherever zF <> 0 (quotient rule B1).  *)
(*  And Cderiv_nonzero_nbhd (B1) upgrades the pointwise line result      *)
(*  zetaC(1+it) <> 0 (ZetaLineNonzero) to: zF <> 0 on a whole disc       *)
(*  around each 1+it (t<>0).  This is the zeta-side input for showing     *)
(*  -zeta'/zeta holomorphic across the boundary.  (The zeta'-side needs   *)
(*  the second derivative of zeta and is deferred.)                      *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CDeriv Holomorphic CHoloCalculus
        ZetaFn ZetaLineNonzero.
Open Scope R_scope.

(* ---- 1+it (t<>0) is in the domain of zeta ---- *)
Lemma line_inDom : forall t, t <> 0 -> inDom (mkC 1 t).
Proof.
  intros t Ht; split; [ cbn [Re]; lra | ].
  intro Hc; apply Ht.
  assert (Him : Im (Cminus C1 (mkC 1 t)) = Im C0) by (rewrite Hc; reflexivity).
  unfold Cminus, C1, C0 in Him; cbn [Im] in Him; lra.
Qed.

(* ---- zeta does not vanish at 1+it ---- *)
Lemma zF_line_nonzero : forall t, t <> 0 -> zF (mkC 1 t) <> C0.
Proof.
  intros t Ht; destruct (line_inDom t Ht) as [H0 H1].
  rewrite (zF_eq (mkC 1 t) H0 H1); exact (zetaC_line_nonzero t Ht H0 H1).
Qed.

(* ---- 1/zeta is holomorphic wherever zeta is nonzero ---- *)
Lemma zF_inv_holo : forall z, inDom z -> zF z <> C0 ->
  exists d, is_Cderiv (fun s => Cinv (zF s)) z d.
Proof.
  intros z Hdom Hnz; destruct (zF_holo z Hdom) as [dz Hdz].
  exists (Cmul (Copp (Cinv (Cmul (zF z) (zF z)))) dz).
  apply Cderiv_invc; [ exact Hdz | exact Hnz ].
Qed.

Corollary zF_inv_holomorphic :
  HolomorphicOn (fun s => Cinv (zF s)) (fun s => inDom s /\ zF s <> C0).
Proof. intros z [Hdom Hnz]; apply zF_inv_holo; [ exact Hdom | exact Hnz ]. Qed.

(* ---- zeta is nonzero on an open disc around each 1+it, t<>0 ---- *)
Theorem zeta_line_open_nonzero : forall t, t <> 0 ->
  exists del, 0 < del /\ forall h, Cmod h < del -> zF (Cadd (mkC 1 t) h) <> C0.
Proof.
  intros t Ht; destruct (zF_holo (mkC 1 t) (line_inDom t Ht)) as [d Hd].
  apply (Cderiv_nonzero_nbhd zF (mkC 1 t) d Hd), zF_line_nonzero; exact Ht.
Qed.

Print Assumptions zeta_line_open_nonzero.

(* ================================================================= *)
(*  END ZetaInvHolo.v  —  1/zeta holomorphic; zeta<>0 on a line nbhd.    *)
(* ================================================================= *)
