(* ================================================================= *)
(*  SelbergCollapse.v  —  RUNG 3c-A: the limsup collapse.              *)
(*                                                                    *)
(*  The mechanical half of the cancellation core.  It isolates the      *)
(*  hard content into ONE hypothesis, `avg_below L`: that the           *)
(*  Lam(d)/d-weighted average of Vrem(N/d) stays a FIXED amount rho      *)
(*  below L,                                                            *)
(*     Sum_{d<=N} (Lam d/d) Vrem(N/d)  <=  (L - rho) ln N  +  C0.        *)
(*                                                                    *)
(*  This is exactly what the hard core (Rungs 3c-B2/B3, via the signed  *)
(*  symmetry + spike blocks + tiny-scale bookkeeping) must establish.    *)
(*  Given it, the collapse is short:                                    *)
(*                                                                    *)
(*    selberg_collapse : is_limsup Vrem L -> avg_below L -> L = 0.       *)
(*                                                                    *)
(*  Proof: feed avg_below into selberg_average (3a) to get              *)
(*  Vrem N <= (L - rho) + O(1/ln N); the is_limsup "infinitely often     *)
(*  Vrem k > L - rho/2" property then forces rho/2 < O(1/ln k) -> 0,     *)
(*  contradiction unless L = 0.  Axiom-clean.                            *)
(*                                                                    *)
(*  With this, the whole PNT is provable modulo the single lemma         *)
(*  `avg_below (limsup Vrem)` (the genuine research core, Rung 3c-B).    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith Lists.List.
Import ListNotations.
Require Import Chebyshev ChebyshevBound ChebyshevPrime VonMangoldtGlobal RealMobius
        SelbergEndgame SelbergAverage LimSup LnLimits.
Open Scope R_scope.

Definition avg_below (L : R) : Prop :=
  exists rho C0, 0 < rho /\ exists K, forall N, (K <= N)%nat ->
    Rls (seq 1 N) (fun d => Lam d / INR d * Vrem (N / d)%nat)
    <= (L - rho) * ln (INR N) + C0.

Theorem selberg_collapse : forall L,
  is_limsup Vrem L -> avg_below L -> L = 0.
Proof.
  intros L Hlim Havgb.
  assert (HL0 : 0 <= L) by (apply (is_limsup_nonneg Vrem L Hlim); apply Vrem_nonneg).
  destruct Havgb as [rho [C0 [Hrho [K Havg]]]].
  destruct (Rle_lt_or_eq_dec 0 L HL0) as [Hpos | Heq]; [ exfalso | symmetry; exact Heq ].
  destruct Hlim as [_ Hb].
  destruct (cv_infty_ln (4 * (Rabs (C0 + (88 + 3 * Kup + 1)) + 1) / rho)) as [N1 HN1].
  destruct (Hb (rho / 2) ltac:(lra) (Nat.max (Nat.max K N1) 2)) as [k [Hk Hgt]].
  assert (HkK : (K <= k)%nat) by lia.
  assert (Hk2 : (2 <= k)%nat) by lia.
  assert (Hlnpos : 0 < ln (INR k)) by (apply ln_INR_pos; lia).
  assert (Hlnk : 4 * (Rabs (C0 + (88 + 3 * Kup + 1)) + 1) / rho < ln (INR k))
    by (apply HN1; lia).
  pose proof (selberg_average k ltac:(lia)) as HSA.
  pose proof (Havg k HkK) as HAV.
  (* Vrem k * ln k <= (L - rho) ln k + (C0 + C) *)
  assert (Hstep : Vrem k * ln (INR k)
                  <= (L - rho) * ln (INR k) + (C0 + (88 + 3 * Kup + 1))) by lra.
  (* Vrem k > L - rho/2, so (L - rho/2) ln k < Vrem k * ln k *)
  assert (HA : (L - rho / 2) * ln (INR k) < Vrem k * ln (INR k))
    by (apply Rmult_lt_compat_r; [ exact Hlnpos | exact Hgt ]).
  (* hence (rho/2) ln k < C0 + C *)
  assert (HC : rho / 2 * ln (INR k) < C0 + (88 + 3 * Kup + 1)) by nra.
  (* but ln k is large enough that (rho/2) ln k >= 2(|C0+C|+1) > C0 + C *)
  assert (HD' : 4 * (Rabs (C0 + (88 + 3 * Kup + 1)) + 1) <= rho * ln (INR k)).
  { apply Rmult_le_reg_l with (/ rho); [ apply Rinv_0_lt_compat; exact Hrho | ].
    replace (/ rho * (rho * ln (INR k))) with (ln (INR k)) by (field; lra).
    replace (/ rho * (4 * (Rabs (C0 + (88 + 3 * Kup + 1)) + 1)))
      with (4 * (Rabs (C0 + (88 + 3 * Kup + 1)) + 1) / rho) by (field; lra).
    left; exact Hlnk. }
  pose proof (Rle_abs (C0 + (88 + 3 * Kup + 1))).
  pose proof (Rabs_pos (C0 + (88 + 3 * Kup + 1))).
  lra.
Qed.

Print Assumptions selberg_collapse.

(* ================================================================= *)
(*  END SelbergCollapse.v  —  RUNG 3c-A: PNT modulo `avg_below`.        *)
(* ================================================================= *)
