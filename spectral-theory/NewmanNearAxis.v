(* ================================================================= *)
(*  NewmanNearAxis.v  —  Newman A3: the near-axis kernel control.         *)
(*                                                                    *)
(*  On the part of the left arc NEAR the imaginary axis (|Re z| <= delta,  *)
(*  Re z <= 0), the kernel is small (|K_R| = 2|Re z|/R^2 <= 2 delta/R^2),   *)
(*  so the integrand is bounded by a quantity proportional to delta          *)
(*  (uniformly in T, since e^{(Re z)T} <= 1 there):                       *)
(*                                                                    *)
(*    gleft_nearaxis : |g(z) e^{zT} K_R(z)| <= 2 M delta / R^2,            *)
(*                                                                    *)
(*  and integrated (gleft_nearaxis_arc) <= 4 M delta (b-a)/R -> 0 as        *)
(*  delta -> 0.  This is the LAST self-contained modulus estimate before    *)
(*  the delta->0, T->oo, R->oo triple limit.  Axiom-clean.               *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CExpKernel CNewmanKernel
        CPathIntegral PerronRemovable NewmanArcML NewmanGLeft.
Open Scope R_scope.

Lemma gleft_nearaxis : forall (gz z : C) (delta M T R : R),
  0 <= delta -> 0 <= T -> Re z <= 0 -> Rabs (Re z) <= delta -> Cmod gz <= M ->
  0 < R -> Cnorm2 z = R * R ->
  Cmod (Cmul gz (Cmul (cexpzt z T) (newman_kernel R z))) <= 2 * M * delta / (R * R).
Proof.
  intros gz z delta M T R Hd HT Hz Hzd HM HR Hcirc.
  rewrite !Cmod_mul, (Cmod_cexpzt z T), (Cmod_newman_kernel R z HR Hcirc).
  apply Rle_trans with (M * (1 * (2 * delta / (R * R)))).
  - apply Rmult_le_compat; [ apply Cmod_nonneg | | exact HM | ].
    + apply Rmult_le_pos; [ left; apply exp_pos | ].
      unfold Rdiv; apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | apply Rabs_pos ] | left; apply Rinv_0_lt_compat; nra ].
    + apply Rmult_le_compat.
      * left; apply exp_pos.
      * unfold Rdiv; apply Rmult_le_pos;
          [ apply Rmult_le_pos; [ lra | apply Rabs_pos ] | left; apply Rinv_0_lt_compat; nra ].
      * rewrite <- exp_0; apply exp_le; nra.
      * unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; nra | ].
        apply Rmult_le_compat_l; [ lra | exact Hzd ].
  - apply Req_le; field; apply Rgt_not_eq; exact HR.
Qed.

Corollary gleft_nearaxis_arc :
  forall (g : C -> C) (R delta M T a b : R)
         (Hf : Ccont (fun u => Cmul
                 (Cmul (g (arc R u)) (Cmul (cexpzt (arc R u) T) (newman_kernel R (arc R u))))
                 (arc' R u))),
  0 < R -> 0 <= delta -> 0 <= T -> a <= b ->
  (forall u, a <= u <= b -> Re (arc R u) <= 0) ->
  (forall u, a <= u <= b -> Rabs (Re (arc R u)) <= delta) ->
  (forall u, a <= u <= b -> Cmod (g (arc R u)) <= M) ->
  Cmod (pathint (arc R) (arc' R)
          (fun z => Cmul (g z) (Cmul (cexpzt z T) (newman_kernel R z))) Hf a b)
  <= 2 * (2 * M * delta / (R * R) * R) * (b - a).
Proof.
  intros g R delta M T a b Hf HR Hd HT Hab HRe HRabs HgM.
  apply (arc_ML (fun z => Cmul (g z) (Cmul (cexpzt z T) (newman_kernel R z))) R a b
           (2 * M * delta / (R * R)) Hf); [ lra | exact Hab | ].
  intros u Hu.
  apply (gleft_nearaxis (g (arc R u)) (arc R u) delta M T R Hd HT
           (HRe u Hu) (HRabs u Hu) (HgM u Hu) HR (Cnorm2_arc R u)).
Qed.

Print Assumptions gleft_nearaxis.

(* ================================================================= *)
(*  END NewmanNearAxis.v — the near-axis O(delta) control.                *)
(*  gleft_decay (away, ->0 as T) + gleft_nearaxis (near, ->0 as delta)    *)
(*  are the two halves of Newman's g-left estimate; splitting the arc at   *)
(*  |Re z| = delta and taking delta->0 then T->oo bounds the whole g-left. *)
(*  All that then remains is Cauchy's formula on the contour + R->oo.      *)
(* ================================================================= *)
