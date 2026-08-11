(* ================================================================= *)
(*  NewmanGLeft.v  —  Newman A3: the g-left dominated-limit piece.        *)
(*                                                                    *)
(*  On the left arc bounded away from the imaginary axis (Re z <= -delta), *)
(*  the g contribution decays exponentially in T:                        *)
(*                                                                    *)
(*    gleft_decay : |g(z) e^{zT} K_R(z)| <= (2M/R) e^{-delta T},           *)
(*                                                                    *)
(*  when |g(z)| <= M and |z| = R.  Integrated over such a sub-arc           *)
(*  (gleft_arc_decay) this -> 0 as T -> oo -- the away-from-axis part of    *)
(*  Newman's g-left estimate (the near-axis part is killed by |K_R| small). *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CExpKernel CNewmanKernel
        CPathIntegral PerronRemovable NewmanArcML.
Open Scope R_scope.

Lemma exp_le : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab; destruct (Rle_lt_or_eq_dec a b Hab) as [H | H];
    [ left; apply exp_increasing; exact H | subst; apply Rle_refl ].
Qed.

(*  the pointwise exponential-decay bound on the left arc  *)
Lemma gleft_decay : forall (gz z : C) (delta M T R : R),
  0 < delta -> 0 <= T -> Re z <= - delta -> Cmod gz <= M ->
  0 < R -> Cnorm2 z = R * R ->
  Cmod (Cmul gz (Cmul (cexpzt z T) (newman_kernel R z))) <= 2 * M / R * exp (- delta * T).
Proof.
  intros gz z delta M T R Hd HT Hz HM HR Hcirc.
  assert (HMnn : 0 <= M) by (eapply Rle_trans; [ apply Cmod_nonneg | exact HM ]).
  assert (HReR : Rabs (Re z) <= R).
  { eapply Rle_trans; [ apply Rabs_Re_le_Cmod | ].
    unfold Cmod; rewrite Hcirc; rewrite sqrt_square; [ apply Rle_refl | lra ]. }
  rewrite !Cmod_mul, (Cmod_cexpzt z T), (Cmod_newman_kernel R z HR Hcirc).
  apply Rle_trans with (M * (exp (- delta * T) * (2 * R / (R * R)))).
  - apply Rmult_le_compat; [ apply Cmod_nonneg | | exact HM | ].
    + apply Rmult_le_pos; [ left; apply exp_pos | ].
      unfold Rdiv; apply Rmult_le_pos;
        [ apply Rmult_le_pos; [ lra | apply Rabs_pos ]
        | left; apply Rinv_0_lt_compat; nra ].
    + apply Rmult_le_compat.
      * left; apply exp_pos.
      * unfold Rdiv; apply Rmult_le_pos;
          [ apply Rmult_le_pos; [ lra | apply Rabs_pos ] | left; apply Rinv_0_lt_compat; nra ].
      * apply exp_le; apply Rmult_le_compat_r; [ exact HT | exact Hz ].
      * unfold Rdiv; apply Rmult_le_compat_r; [ left; apply Rinv_0_lt_compat; nra | ].
        apply Rmult_le_compat_l; [ lra | exact HReR ].
  - apply Req_le; field; apply Rgt_not_eq; exact HR.
Qed.

(*  integrated over a sub-arc bounded away from the axis: -> 0 as T -> oo  *)
Lemma Cnorm2_arc : forall R u, Cnorm2 (arc R u) = R * R.
Proof.
  intros R u; unfold arc, Cnorm2; cbn [Re Im].
  replace (R * cos u * (R * cos u) + R * sin u * (R * sin u))
    with (R * R * (cos u * cos u + sin u * sin u)) by ring.
  assert (Hp : cos u * cos u + sin u * sin u = 1)
    by (pose proof (sin2_cos2 u); unfold Rsqr in *; lra).
  rewrite Hp; ring.
Qed.

Corollary gleft_arc_decay :
  forall (g : C -> C) (R delta M T a b : R)
         (Hf : Ccont (fun u => Cmul
                 (Cmul (g (arc R u)) (Cmul (cexpzt (arc R u) T) (newman_kernel R (arc R u))))
                 (arc' R u))),
  0 < R -> 0 < delta -> 0 <= T -> a <= b ->
  (forall u, a <= u <= b -> Re (arc R u) <= - delta) ->
  (forall u, a <= u <= b -> Cmod (g (arc R u)) <= M) ->
  Cmod (pathint (arc R) (arc' R)
          (fun z => Cmul (g z) (Cmul (cexpzt z T) (newman_kernel R z))) Hf a b)
  <= 2 * (2 * M / R * exp (- delta * T) * R) * (b - a).
Proof.
  intros g R delta M T a b Hf HR Hd HT Hab HRez HgM.
  apply (arc_ML (fun z => Cmul (g z) (Cmul (cexpzt z T) (newman_kernel R z))) R a b
           (2 * M / R * exp (- delta * T)) Hf); [ lra | exact Hab | ].
  intros u Hu.
  apply (gleft_decay (g (arc R u)) (arc R u) delta M T R Hd HT
           (HRez u Hu) (HgM u Hu) HR (Cnorm2_arc R u)).
Qed.

Print Assumptions gleft_decay.

(* ================================================================= *)
(*  END NewmanGLeft.v — the g-left exponential decay (away from axis).    *)
(*  gleft_arc_decay -> 0 as T -> oo (fixed R, delta).  The near-axis part  *)
(*  (|Re z| < delta) is controlled by |K_R| <= 2 delta/R^2; the delta ->    *)
(*  0 then T -> oo double limit assembles Newman's g-left estimate.         *)
(* ================================================================= *)
