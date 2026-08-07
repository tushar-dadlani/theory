(* ================================================================= *)
(*  CHoloCalculus.v  —  Milestone B, brick B1: the missing holomorphy  *)
(*  calculus.  The product/chain/inverse rules already exist            *)
(*  (Cderiv_mul, Cderiv_comp, Cderiv_inv); here we add                  *)
(*    - Cderiv_invc : reciprocal 1/G(w) of a holomorphic G with G z<>0  *)
(*    - Cderiv_div  : quotient F/G                                       *)
(*    - is_Cderiv_cont : complex-differentiable => continuous            *)
(*    - Cderiv_nonzero_nbhd : F continuous & F z<>0 => F<>0 on a disc.    *)
(*  The last is exactly what upgrades the POINTWISE zetaC(1+it)<>0 to    *)
(*  non-vanishing on an OPEN neighborhood of the line, needed for        *)
(*  holomorphy of -zeta'/zeta across Re s = 1.                           *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus Holomorphic CDeriv.
Open Scope R_scope.

(* ---- reciprocal rule:  d/dw [1 / G(w)] = -G'(z) / G(z)^2 ---- *)
Lemma Cderiv_invc : forall G z dG, is_Cderiv G z dG -> G z <> C0 ->
  is_Cderiv (fun w => Cinv (G w)) z (Cmul (Copp (Cinv (Cmul (G z) (G z)))) dG).
Proof.
  intros G z dG HG Hnz.
  apply (Cderiv_comp Cinv G z (Copp (Cinv (Cmul (G z) (G z)))) dG);
    [ apply Cderiv_inv; exact Hnz | exact HG ].
Qed.

(* ---- quotient rule:  d/dw [F/G] = F'/G + F*(-G'/G^2) ---- *)
Lemma Cderiv_div : forall F G z dF dG,
  is_Cderiv F z dF -> is_Cderiv G z dG -> G z <> C0 ->
  is_Cderiv (fun w => Cmul (F w) (Cinv (G w))) z
    (Cadd (Cmul dF (Cinv (G z)))
          (Cmul (F z) (Cmul (Copp (Cinv (Cmul (G z) (G z)))) dG))).
Proof.
  intros F G z dF dG HF HG Hnz.
  apply (Cderiv_mul F (fun w => Cinv (G w)) z dF
           (Cmul (Copp (Cinv (Cmul (G z) (G z)))) dG));
    [ exact HF | apply Cderiv_invc; [ exact HG | exact Hnz ] ].
Qed.

(* ---- differentiability implies continuity ---- *)
Lemma is_Cderiv_cont : forall F z d, is_Cderiv F z d ->
  forall eps, 0 < eps -> exists del, 0 < del /\
    forall h, Cmod h < del -> Cmod (Cminus (F (Cadd z h)) (F z)) < eps.
Proof.
  intros F z d HF eps Heps.
  destruct (HF 1 Rlt_0_1) as [del0 [Hdel0 HF1]].
  set (B := 1 + Cmod d).
  assert (HB : 0 < B) by (unfold B; pose proof (Cmod_nonneg d); lra).
  exists (Rmin del0 (eps / (B + 1))).
  split; [ apply Rmin_glb_lt; [ exact Hdel0 | apply Rdiv_lt_0_compat; lra ] | ].
  intros h Hh.
  assert (Hh0 : Cmod h < del0) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_l ]).
  assert (HhB : Cmod h < eps / (B + 1)) by (eapply Rlt_le_trans; [ exact Hh | apply Rmin_r ]).
  assert (Hbound : Cmod (Cminus (F (Cadd z h)) (F z)) <= B * Cmod h).
  { replace (Cminus (F (Cadd z h)) (F z))
      with (Cadd (Cminus (Cminus (F (Cadd z h)) (F z)) (Cmul d h)) (Cmul d h)) by ring.
    eapply Rle_trans; [ apply Cmod_triangle | ].
    rewrite Cmod_mul; pose proof (HF1 h Hh0); pose proof (Cmod_nonneg h); unfold B; nra. }
  assert (Hkey : (B + 1) * Cmod h < eps).
  { replace eps with ((B + 1) * (eps / (B + 1))) by (field; lra).
    apply Rmult_lt_compat_l; [ lra | exact HhB ]. }
  pose proof (Cmod_nonneg h); nra.
Qed.

(* ---- non-vanishing on a neighborhood ---- *)
Lemma Cderiv_nonzero_nbhd : forall F z d, is_Cderiv F z d -> F z <> C0 ->
  exists del, 0 < del /\ forall h, Cmod h < del -> F (Cadd z h) <> C0.
Proof.
  intros F z d HF Hnz.
  destruct (is_Cderiv_cont F z d HF (Cmod (F z)) (Cmod_pos_ne0 (F z) Hnz))
    as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ].
  intros h Hh Hcontra; specialize (Hc h Hh); rewrite Hcontra in Hc.
  replace (Cminus C0 (F z)) with (Copp (F z)) in Hc by ring.
  rewrite Cmod_opp in Hc; lra.
Qed.

Print Assumptions Cderiv_div.
Print Assumptions Cderiv_nonzero_nbhd.

(* ================================================================= *)
(*  END CHoloCalculus.v  —  quotient rule + open non-vanishing.        *)
(* ================================================================= *)
