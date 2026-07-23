(* ================================================================= *)
(*  FermatTwoSquares.v                                               *)
(*                                                                    *)
(*  FERMAT'S TWO-SQUARE THEOREM:  every prime p = 1 (mod 4) is a sum   *)
(*  of two squares,  p = a^2 + b^2.                                    *)
(*                                                                    *)
(*  Proof by EULER'S DESCENT, whose engine is Brahmagupta-Fibonacci    *)
(*  (= Gaussian-norm multiplicativity, SumTwoSquares.sum2_mul):        *)
(*                                                                    *)
(*   - SumTwoSquares.neg1_QR gives x with p | x^2 + 1 (using the        *)
(*     from-scratch cyclicity of the units mod p.  Reducing x to a       *)
(*     nearest residue u (|2u| <= p) yields m*p = u^2+1, 0 < m < p.       *)
(*     residue u (|2u| <= p) yields  m*p = u^2 + 1  with 0 < m < p.     *)
(*   - DESCENT STEP (descent_step): from m*p = a^2+b^2 with 1 < m < p    *)
(*     (p prime), choosing u = a, v = b (mod m) of least abs. value      *)
(*     gives u^2+v^2 = m*r with 0 < r < m, and Brahmagupta turns         *)
(*        (a^2+b^2)(u^2+v^2) = (au+bv)^2 + (av-bu)^2                     *)
(*     -- whose factors are divisible by m -- into  r*p = A^2 + B^2.     *)
(*     r <> 0 because otherwise m | a, m | b  =>  m | p, impossible      *)
(*     for a prime with 1 < m < p (prime_divisors).                     *)
(*   - Iterating the strictly-decreasing m (descent_fuel, induction on   *)
(*     a nat bound) reaches m = 1, i.e. p = A^2 + B^2.                   *)
(*                                                                    *)
(*  Footprint: same as SumTwoSquares -- axiom-free ("Closed under the   *)
(*  global context"): nat/Z arithmetic + Znumtheory, on top of the      *)
(*  repo's from-scratch cyclicity tower.                              *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia.
Require Import SumTwoSquares.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Two small Z utilities                                            *)
(* ----------------------------------------------------------------- *)

(* nearest residue: some u = a (mod m) with |2u| <= m *)
Lemma nearest_rep : forall m a, 0 < m -> exists u, (m | a - u) /\ - m <= 2 * u <= m.
Proof.
  intros m a Hm.
  pose proof (Z.mod_pos_bound a m Hm) as Hb.
  destruct (Z_le_gt_dec (2 * (a mod m)) m) as [Hle|Hgt].
  - exists (a mod m); split; [ | lia ].
    exists (a / m); rewrite (Z.div_mod a m) at 1 by lia; ring.
  - exists (a mod m - m); split; [ | lia ].
    exists (a / m + 1); rewrite (Z.div_mod a m) at 1 by lia; ring.
Qed.

Lemma Zcancel : forall k x y, k <> 0 -> k * x = k * y -> x = y.
Proof. intros k x y Hk H; apply (Z.mul_reg_l x y k Hk H). Qed.

(* ================================================================= *)
(*  The descent, for a fixed prime p                                 *)
(* ================================================================= *)

Section Fermat.

Variable p : Z.
Hypothesis Hp : prime p.

Lemma Hpge2 : 2 <= p.
Proof. apply prime_ge_2; exact Hp. Qed.

(* ONE DESCENT STEP: 1 < m < p, m*p = a^2+b^2  =>  r*p = A^2+B^2, r < m *)
Lemma descent_step : forall m a b, 1 < m -> m < p -> m * p = a * a + b * b ->
  exists r A B, 0 < r < m /\ r * p = A * A + B * B.
Proof.
  intros m a b Hm1 Hmp Heq.
  assert (Hm0 : 0 < m) by lia.
  destruct (nearest_rep m a Hm0) as [u [Hu Hub]].
  destruct (nearest_rep m b Hm0) as [v [Hv Hvb]].
  (* m divides the three combinations *)
  assert (Hdr : (m | u * u + v * v)).
  { replace (u * u + v * v)
      with ((a * a + b * b) - ((a - u) * (a + u) + (b - v) * (b + v))) by ring.
    apply Z.divide_sub_r.
    - rewrite <- Heq; apply Z.divide_factor_l.
    - apply Z.divide_add_r; apply Z.divide_mul_l; [ exact Hu | exact Hv ]. }
  assert (HdA : (m | a * u + b * v)).
  { replace (a * u + b * v)
      with ((a * a + b * b) - (a * (a - u) + b * (b - v))) by ring.
    apply Z.divide_sub_r.
    - rewrite <- Heq; apply Z.divide_factor_l.
    - apply Z.divide_add_r; apply Z.divide_mul_r; [ exact Hu | exact Hv ]. }
  assert (HdB : (m | a * v - b * u)).
  { replace (a * v - b * u) with (b * (a - u) - a * (b - v)) by ring.
    apply Z.divide_sub_r; apply Z.divide_mul_r; [ exact Hu | exact Hv ]. }
  destruct Hdr as [r Hr]; destruct HdA as [A HA]; destruct HdB as [B HB].
  exists r, A, B.
  (* r*p = A^2 + B^2, by cancelling m^2 from Brahmagupta *)
  assert (Hcancel : m * m * (p * r) = m * m * (A * A + B * B)).
  { replace (m * m * (A * A + B * B)) with ((A * m) * (A * m) + (B * m) * (B * m)) by ring.
    rewrite <- HA, <- HB.
    replace (m * m * (p * r)) with ((m * p) * (r * m)) by ring.
    rewrite <- Hr, Heq; ring. }
  assert (HprAB : p * r = A * A + B * B) by (apply (Zcancel (m * m)); [ nia | exact Hcancel ]).
  (* bounds on r *)
  assert (Hr_nonneg : 0 <= r) by nia.
  assert (Hr_lt : r < m) by nia.
  assert (Hr_pos : 0 < r).
  { destruct (Z.eq_dec r 0) as [Er|Er]; [ | lia ].
    exfalso; subst r.
    assert (Hu0 : u = 0) by nia.
    assert (Hv0 : v = 0) by nia.
    assert (Hma : (m | a)) by (destruct Hu as [c Hc]; exists c; lia).
    assert (Hmb : (m | b)) by (destruct Hv as [c Hc]; exists c; lia).
    destruct Hma as [ka Hka]; destruct Hmb as [kb Hkb].
    assert (Hmpdvd : (m | p)).
    { exists (ka * ka + kb * kb).
      apply (Zcancel m); [ lia | ].
      rewrite Heq, Hka, Hkb; ring. }
    pose proof Hpge2.
    destruct (prime_divisors p Hp m Hmpdvd) as [Hd|[Hd|[Hd|Hd]]]; lia. }
  split; [ lia | ].
  rewrite <- HprAB; ring.
Qed.

(* DESCENT by induction on a nat bound for m *)
Lemma descent_fuel : forall n m a b, (Z.to_nat m <= n)%nat ->
  0 < m -> m < p -> m * p = a * a + b * b -> exists A B, p = A * A + B * B.
Proof.
  induction n as [|n IH]; intros m a b Hn Hm0 Hmp Heq.
  - lia.
  - destruct (Z.eq_dec m 1) as [E|E].
    + exists a, b; subst m; lia.
    + destruct (descent_step m a b ltac:(lia) Hmp Heq) as [r [A [B [Hr Hrp]]]].
      apply (IH r A B); [ lia | lia | lia | exact Hrp ].
Qed.

(* the descent packaged: any proper multiple m*p (0<m<p) that is a sum   *)
(* of two squares forces p itself to be a sum of two squares.            *)
Theorem fermat_core : forall m a b, 0 < m -> m < p -> m * p = a * a + b * b ->
  exists A B, p = A * A + B * B.
Proof.
  intros m a b Hm0 Hmp Heq.
  apply (descent_fuel (S (Z.to_nat m)) m a b); [ lia | assumption | assumption | assumption ].
Qed.

End Fermat.

(* ================================================================= *)
(*  THE THEOREM: prime p = 1 (mod 4)  =>  p = a^2 + b^2               *)
(* ================================================================= *)

Theorem fermat_two_squares : forall pn : nat,
  prime (Z.of_nat pn) -> (pn mod 4 = 1)%nat ->
  exists a b : Z, Z.of_nat pn = a * a + b * b.
Proof.
  intros pn Hp Hmod.
  set (p := Z.of_nat pn) in *.
  assert (Hpge2 : 2 <= p) by (apply prime_ge_2; exact Hp).
  (* 4 | pn - 1 *)
  assert (Hdiv4 : Nat.divide 4 (pn - 1)).
  { pose proof (Nat.div_mod_eq pn 4) as Hdm.
    exists (pn / 4)%nat; lia. }
  (* -1 is a QR: pn | x^2 + 1 *)
  destruct (neg1_QR pn Hp Hdiv4) as [x Hx].
  assert (Hnd : Nat.divide pn (x * x + 1)) by (apply Nat.Lcm0.mod_divide; exact Hx).
  destruct Hnd as [k Hk].
  assert (HpX : (p | Z.of_nat x * Z.of_nat x + 1)).
  { exists (Z.of_nat k); unfold p; nia. }
  (* reduce x to a nearest residue u with |2u| <= p *)
  destruct (nearest_rep p (Z.of_nat x) ltac:(lia)) as [u [Hu Hub]].
  assert (HuX : (p | u - Z.of_nat x)) by (destruct Hu as [c Hc]; exists (- c); lia).
  assert (Hpu : (p | u * u + 1)).
  { replace (u * u + 1)
      with ((Z.of_nat x * Z.of_nat x + 1) + (u - Z.of_nat x) * (u + Z.of_nat x)) by ring.
    apply Z.divide_add_r; [ exact HpX | apply Z.divide_mul_l; exact HuX ]. }
  destruct Hpu as [m Hm].
  (* 0 < m < p, and m*p = u^2 + 1^2 *)
  assert (Hm0 : 0 < m) by nia.
  assert (Hmlt : m < p) by nia.
  destruct (fermat_core p Hp m u 1 Hm0 Hmlt ltac:(nia)) as [A [B HAB]].
  exists A, B; exact HAB.
Qed.

Print Assumptions fermat_two_squares.

(* ================================================================= *)
(*  END FermatTwoSquares.v                                           *)
(*  Fermat's two-square theorem p = 1 (mod 4) => p = a^2+b^2, by       *)
(*  Euler descent with Brahmagupta-Fibonacci (Gaussian-norm            *)
(*  multiplicativity) as its engine and the from-scratch cyclicity     *)
(*  (neg1_QR) as its seed.  Closed under the global context.          *)
(* ================================================================= *)
