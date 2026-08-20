(* ================================================================= *)
(*  XiSumBounds.v  —  the two dyadic sums, instantiated at xi.         *)
(*                                                                    *)
(*    xi_sum_inv1 : SUM 1/|rho| over zeros of modulus < 2^K, counted   *)
(*      with multiplicity, is at most agrow . K(K+1)/2.                *)
(*    xi_sum_tail : SUM 1/|rho|^2 over zeros of modulus in             *)
(*      [2^K, 2^N) is at most agrow . 2(K+2)/2^K.                      *)
(*                                                                    *)
(*  Same counting majorant Bxi and the same growth theorem xi_Hgrow    *)
(*  as the genus-1 convergence bound -- nothing new is assumed.  These *)
(*  are the two blocks of the minimum-modulus estimate for the         *)
(*  Hadamard product: near zeros contribute through Re(z/rho), which   *)
(*  is controlled by the first-power sum, and far zeros through        *)
(*  |z/rho|^2, which is controlled by the tail.                        *)
(*  Axiom-clean.                                                       *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia List.
Require Import ComplexField Cmodulus CDyadicSum CDyadicSum2
        JensenMultiZero CZeroListFactor RiemannXiEntire
        XiZeroCount XiZeroDensity XiHgrow.
Open Scope R_scope.

Theorem xi_sum_inv1 : forall (K : nat) (s : list C),
  XiPeel s ->
  (forall x, In x s -> XiC x = C0) ->
  (forall x, In x s -> 1 <= Cmod x < 2 ^ K) ->
  sumlist invmod s <= agrow * Aser K.
Proof.
  intros K s Hpeel HP Hrange.
  exact (dyadic_sum_inv1 (fun z => XiC z = C0) Bxi XiPeel XiPeel_filter
           (fun r s' Hr Hq _ Hsm => xi_count_peel r s' Hr Hq Hsm)
           agrow xi_Hgrow K s Hpeel HP Hrange).
Qed.

Theorem xi_sum_tail : forall (K N : nat), (K <= N)%nat ->
  forall s : list C,
  XiPeel s ->
  (forall x, In x s -> XiC x = C0) ->
  (forall x, In x s -> 2 ^ K <= Cmod x < 2 ^ N) ->
  sumlist invsq s <= agrow * (2 * (INR K + 2) / 2 ^ K).
Proof.
  intros K N HKN s Hpeel HP Hrange.
  exact (dyadic_sum_tail (fun z => XiC z = C0) Bxi XiPeel XiPeel_filter
           (fun r s' Hr Hq _ Hsm => xi_count_peel r s' Hr Hq Hsm)
           agrow agrow_nonneg xi_Hgrow K N HKN s Hpeel HP Hrange).
Qed.

Print Assumptions xi_sum_inv1.
Print Assumptions xi_sum_tail.
