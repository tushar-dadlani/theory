(* ================================================================= *)
(*  ZeroFreeOpt.v  --  the optimisation, and the feed into depth.      *)
(*                                                                    *)
(*    quartic_opt : 0 < K, 0 <= u,                                    *)
(*        (81/(256K))^3 <= K (u + 81/(256K))^4   ==>  27/(256K) <= u   *)
(*                                                                    *)
(*    depth_of_region : 0 < w <= 1/2, 0 < Re z, Re z <= 1 - w         *)
(*        ==>  depth z <= ln (/ w)                                     *)
(*                                                                    *)
(*  quartic_opt is the choice of a = 1 + delta in the zero-free-region *)
(*  argument, done exactly.  Chaining CHorizMVT.horiz_mvt (which gives *)
(*  |zeta(a+i.gamma)| <= 2(a-beta) M) against the 3-4-1 lower bound    *)
(*  (which gives (a-1)^3 <= A |zeta(a+i.gamma)|^4) yields              *)
(*                                                                    *)
(*      delta^3 <= K (u + delta)^4,     u = 1 - beta,  K = 16 A M^4,   *)
(*                                                                    *)
(*  and the region is whatever lower bound on u that forces.           *)
(*                                                                    *)
(*  The continuous optimum is delta = 81/(256K), giving u >= 27/(256K),*)
(*  and the striking thing is that at that delta the two sides meet    *)
(*  EXACTLY: the contradiction needs 108^4 <= 81^3 * 256, and          *)
(*  108^4 = 136048896 = 531441 * 256 = 81^3 * 256.  So no fourth root  *)
(*  ever has to be taken -- the whole optimisation is rational         *)
(*  arithmetic, and the constant 27/256 is sharp for this argument.    *)
(*  (Had the numbers not met, one would be stuck approximating         *)
(*  (delta^3/K)^{1/4}, which in Coq means Rpower and a great deal of   *)
(*  avoidable pain.)                                                  *)
(*                                                                    *)
(*  depth_of_region converts a region into the coordinate of           *)
(*  CriticalDepth: a strip Re z <= 1 - w is a depth bound ln(1/w),     *)
(*  so K ~ ln^9 T gives depth <= 9 ln ln T + O(1).  Axiom-clean.       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra.
Require Import ComplexField Cmodulus RiemannXiEntire SpectralReflectionBridge
        ZetaOpenStrip CriticalDepth.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(*  A.  THE OPTIMISATION                                               *)
(* ----------------------------------------------------------------- *)
Theorem quartic_opt : forall u K, 0 < K -> 0 <= u ->
  (81 / (256 * K)) ^ 3 <= K * (u + 81 / (256 * K)) ^ 4 ->
  27 / (256 * K) <= u.
Proof.
  intros u K HK Hu H.
  destruct (Rle_or_lt (27 / (256 * K)) u) as [Hge | Hlt]; [ exact Hge | exfalso ].
  assert (HKpos : 0 < 256 * K) by lra.
  assert (HD : 0 < 81 / (256 * K)) by (apply Rdiv_lt_0_compat; lra).
  assert (Hb : 0 < 108 / (256 * K)) by (apply Rdiv_lt_0_compat; lra).
  (* 27/(256K) + 81/(256K) = 108/(256K) *)
  assert (Hsum : u + 81 / (256 * K) < 108 / (256 * K)).
  { assert (E : 27 / (256 * K) + 81 / (256 * K) = 108 / (256 * K))
      by (field; lra).
    lra. }
  assert (Hpos : 0 < u + 81 / (256 * K)) by lra.
  assert (H2 : (u + 81 / (256 * K)) * (u + 81 / (256 * K))
             < (108 / (256 * K)) * (108 / (256 * K)))
    by (apply Rmult_le_0_lt_compat; lra).
  assert (H4 : (u + 81 / (256 * K)) ^ 4 < (108 / (256 * K)) ^ 4).
  { replace ((u + 81 / (256 * K)) ^ 4)
      with (((u + 81 / (256 * K)) * (u + 81 / (256 * K)))
            * ((u + 81 / (256 * K)) * (u + 81 / (256 * K)))) by ring.
    replace ((108 / (256 * K)) ^ 4)
      with (((108 / (256 * K)) * (108 / (256 * K)))
            * ((108 / (256 * K)) * (108 / (256 * K)))) by ring.
    apply Rmult_le_0_lt_compat; nra. }
  (* the exact meeting point: 108^4 = 81^3 * 256 *)
  assert (Hkey : K * (108 / (256 * K)) ^ 4 = (81 / (256 * K)) ^ 3)
    by (field; lra).
  assert (Hmul : K * (u + 81 / (256 * K)) ^ 4 < K * (108 / (256 * K)) ^ 4)
    by (apply Rmult_lt_compat_l; [ exact HK | exact H4 ]).
  lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  a region IS a depth bound                                      *)
(* ----------------------------------------------------------------- *)
Lemma ln_le_loc : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [H | H].
  - left. apply ln_increasing; assumption.
  - subst y. lra.
Qed.

Theorem depth_of_region : forall z w, 0 < w -> w <= / 2 ->
  0 < Re z -> Re z <= 1 - w -> depth z <= ln (/ w).
Proof.
  intros z w Hw0 Hw2 Hz0 Hz1.
  assert (Hlt1 : Re z < 1) by lra.
  assert (Hmid : 0 < 1 - w < 1) by lra.
  assert (Hstep : depth z <= logit (1 - w))
    by (unfold depth; apply (logit_le_iff (Re z) (1 - w)); [ lra | lra | lra ]).
  assert (Hval : logit (1 - w) <= ln (/ w)).
  { unfold logit.
    replace (1 - (1 - w)) with w by ring.
    apply ln_le_loc.
    - apply Rdiv_lt_0_compat; lra.
    - assert (E : / w = 1 / w) by (unfold Rdiv; ring).
      rewrite E. unfold Rdiv. apply Rmult_le_compat_r; [ | lra ].
      left; apply Rinv_0_lt_compat; lra. }
  lra.
Qed.

(* the shape the chain produces: w = 27/(256 K) *)
Corollary depth_of_quartic : forall z K, 0 < K -> 54 <= 256 * K ->
  0 < Re z -> Re z <= 1 - 27 / (256 * K) ->
  depth z <= ln (256 * K / 27).
Proof.
  intros z K HK H54 Hz0 Hz1.
  assert (Hw0 : 0 < 27 / (256 * K)) by (apply Rdiv_lt_0_compat; lra).
  assert (Hw2 : 27 / (256 * K) <= / 2).
  { apply (Rmult_le_reg_r (256 * K)); [ lra | ].
    assert (E : 27 / (256 * K) * (256 * K) = 27) by (field; lra).
    rewrite E. lra. }
  pose proof (depth_of_region z (27 / (256 * K)) Hw0 Hw2 Hz0 Hz1) as H.
  assert (E : / (27 / (256 * K)) = 256 * K / 27) by (field; lra).
  rewrite E in H. exact H.
Qed.

Print Assumptions quartic_opt.
Print Assumptions depth_of_region.
Print Assumptions depth_of_quartic.
