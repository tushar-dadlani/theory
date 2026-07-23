(* ================================================================= *)
(*  SelfPowerDynamics.v                                              *)
(*                                                                    *)
(*  THE DYNAMICS OF THE SELF-POWER MAP  x |-> x^x mod p  on F_p*.      *)
(*                                                                    *)
(*  Building on FpField (selfpow p x = pw p x x = x^x mod p), we treat *)
(*  self-exponentiation as a discrete dynamical system on the finite   *)
(*  set of units {1..p-1} and prove -- carefully -- the facts that      *)
(*  make it one:                                                      *)
(*                                                                    *)
(*   * EXPONENT REDUCTION (the crux, base vs. exponent):              *)
(*       x^x mod p = pw p x (x mod (p-1))                             *)
(*     the EXPONENT reduces mod p-1 (Fermat), the BASE stays x.  This  *)
(*     predicts step(p-1) = (-1)^(p-1) = 1 for odd p, since            *)
(*     (p-1) mod (p-1) = 0.                                           *)
(*   * UNIT CLOSURE: step maps units to units, so the dynamics lives   *)
(*     on the finite group F_p*.                                      *)
(*   * BOUNDARY: selfpow p 0 = 1 is only the 0^0 = 1 nat convention    *)
(*     (0 is not a unit); selfpow p 1 = 1 (genuine fixed point).       *)
(*   * FIXED POINTS: x^x = x  <=>  x^(x-1) = 1  <=>  ord(x) | (x-1).    *)
(*     (No uniqueness is claimed -- there can be several.)             *)
(*   * EVENTUAL PERIODICITY: every orbit collides within p steps       *)
(*     (pigeonhole on the p-1 units) and is periodic after a possible  *)
(*     pre-period tail.                                               *)
(*                                                                    *)
(*  Axiom-free ("Closed under the global context"), on the from-scratch *)
(*  cyclicity tower.                                                  *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool.
Require Import ZmodPStar ZmodOrder PrimitiveRoot DirichletModP FpField.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(*  §1  EXPONENT REDUCTION  (base stays x, exponent reduces mod p-1)  *)
(* ================================================================= *)

Lemma selfpow_exp_reduce : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  selfpow p x = pw p x (x mod (p - 1)).
Proof. intros p x Hp Hx; unfold selfpow; apply pw_mod_pm1; assumption. Qed.

(* the largest unit maps to 1:  (p-1)^(p-1) = 1  ((-1)^even for odd p) *)
Lemma selfpow_pm1 : forall p, prime (Z.of_nat p) -> selfpow p (p - 1) = 1.
Proof.
  intros p Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  rewrite (selfpow_exp_reduce p (p - 1) Hp ltac:(lia)).
  rewrite Nat.Div0.mod_same; apply pw_0; exact Hp2.
Qed.

(* ================================================================= *)
(*  §2  BOUNDARY / COLLAPSE                                          *)
(* ================================================================= *)

(* selfpow p 0 = 1 is the 0^0 = 1 convention; 0 is not a unit. *)
Lemma selfpow_0 : forall p, 2 <= p -> selfpow p 0 = 1.
Proof.
  intros p Hp; unfold selfpow, pw; rewrite Nat.pow_0_r, Nat.mod_1_l by lia; reflexivity.
Qed.

(* selfpow p 1 = 1 (genuine fixed point) -- from FpField.selfpow_1 *)

(* ================================================================= *)
(*  §3  UNIT CLOSURE: the dynamics stays on F_p*                      *)
(* ================================================================= *)

Lemma selfpow_unit : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  1 <= selfpow p x <= p - 1.
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  unfold selfpow, pw; split.
  - assert (Hnd : ~ Nat.divide p (x ^ x))
      by (apply not_div_pow; [ assumption | apply unit_not_div; exact Hx ]).
    destruct (x ^ x mod p) eqn:E; [ | lia ].
    exfalso; apply Hnd, (proj1 (Nat.Lcm0.mod_divide _ p)); exact E.
  - pose proof (Nat.mod_upper_bound (x ^ x) p ltac:(lia)); lia.
Qed.

(* ================================================================= *)
(*  §4  FIXED POINTS:  x^x = x  <=>  x^(x-1) = 1  <=>  ord(x) | x-1    *)
(* ================================================================= *)

Lemma selfpow_fixed_iff : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  (selfpow p x = x <-> pw p x (x - 1) = 1).
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hxx : x ^ x = x * x ^ (x - 1))
    by (replace x with (1 + (x - 1)) at 2 by lia;
        rewrite Nat.pow_add_r, Nat.pow_1_r; f_equal; lia).
  assert (Ha : ~ Nat.divide p x) by (apply unit_not_div; exact Hx).
  split.
  - (* selfpow p x = x  =>  pw p x (x-1) = 1 *)
    intro Hfix.
    assert (Hc : (x * pw p x (x - 1)) mod p = (x * 1) mod p).
    { unfold pw; rewrite Nat.Div0.mul_mod_idemp_r, <- Hxx.
      change (selfpow p x) with (pw p x x) in Hfix; unfold pw in Hfix.
      rewrite Hfix, Nat.mul_1_r, (Nat.mod_small x p) by lia; reflexivity. }
    pose proof (cancel_mod p x (pw p x (x - 1)) 1 Hp Ha Hc) as Hm.
    unfold pw in Hm |- *.
    rewrite (Nat.mod_small (x ^ (x - 1) mod p) p),
            (Nat.mod_small 1 p) in Hm by (try apply Nat.mod_upper_bound; lia).
    exact Hm.
  - (* pw p x (x-1) = 1  =>  selfpow p x = x *)
    intro Hpw; change (selfpow p x) with (pw p x x); unfold pw.
    rewrite Hxx, <- Nat.Div0.mul_mod_idemp_r.
    change (x ^ (x - 1) mod p) with (pw p x (x - 1)); rewrite Hpw.
    rewrite Nat.mul_1_r; apply Nat.mod_small; lia.
Qed.

Lemma selfpow_fixed_ord : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  (selfpow p x = x <-> Nat.divide (ord p x) (x - 1)).
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  rewrite (selfpow_fixed_iff p x Hp Hx); split.
  - intro Hpw; apply ord_divides; assumption.
  - intros [m Hm]; rewrite Hm, Nat.mul_comm; apply pw_pow_ord_mul;
      [ exact Hp2 | apply ord_period; assumption ].
Qed.

(* x = 1 is a fixed point (x - 1 = 0, so ord(x) | 0 trivially) *)
Lemma selfpow_fixed_1 : forall p, 2 <= p -> selfpow p 1 = 1.
Proof. exact selfpow_1. Qed.

(* ================================================================= *)
(*  §5  ORBITS and EVENTUAL PERIODICITY                              *)
(* ================================================================= *)

Definition orbit (p x k : nat) : nat := Nat.iter k (selfpow p) x.

Lemma orbit_0 : forall p x, orbit p x 0 = x.
Proof. reflexivity. Qed.

Lemma orbit_S : forall p x k, orbit p x (S k) = selfpow p (orbit p x k).
Proof. intros p x k; unfold orbit; rewrite Nat.iter_succ; reflexivity. Qed.

Lemma orbit_unit : forall p x k, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  1 <= orbit p x k <= p - 1.
Proof.
  intros p x k Hp Hx; induction k as [|k IH].
  - rewrite orbit_0; exact Hx.
  - rewrite orbit_S; apply selfpow_unit; assumption.
Qed.

(* the orbit is shift-invariant once two indices agree *)
Lemma orbit_shift : forall p x i j, orbit p x i = orbit p x j ->
  forall e, orbit p x (i + e) = orbit p x (j + e).
Proof.
  intros p x i j Hij e; induction e as [|e IH].
  - rewrite !Nat.add_0_r; exact Hij.
  - replace (i + S e) with (S (i + e)) by lia; replace (j + S e) with (S (j + e)) by lia.
    rewrite !orbit_S, IH; reflexivity.
Qed.

(* the pigeonhole search: is there a collision among the first p iterates? *)
Definition has_coll (p x : nat) : bool :=
  existsb (fun i => existsb (fun j => (i <? j) && (orbit p x i =? orbit p x j)) (seq 0 p))
          (seq 0 p).

(* COLLISION: p iterates into p-1 units must repeat *)
Lemma orbit_collision : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  exists i j, i < j /\ j <= p - 1 /\ orbit p x i = orbit p x j.
Proof.
  intros p x Hp Hx; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  assert (Hcoll : has_coll p x = true).
  { destruct (has_coll p x) eqn:E; [ reflexivity | exfalso ].
    (* E : has_coll = false  =>  orbit injective on [0,p) *)
    assert (Hinj : forall i j, In i (seq 0 p) -> In j (seq 0 p) ->
                     orbit p x i = orbit p x j -> i = j).
    { intros i j Hi Hj Hij; apply in_seq in Hi; apply in_seq in Hj.
      destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hgt]]; [ exfalso | exact Heq | exfalso ].
      - assert (has_coll p x = true).
        { unfold has_coll; apply existsb_exists; exists i; split; [ apply in_seq; lia | ].
          apply existsb_exists; exists j; split; [ apply in_seq; lia | ].
          apply andb_true_intro; split;
            [ apply Nat.ltb_lt; lia | apply Nat.eqb_eq; exact Hij ]. }
        rewrite E in H; discriminate.
      - assert (has_coll p x = true).
        { unfold has_coll; apply existsb_exists; exists j; split; [ apply in_seq; lia | ].
          apply existsb_exists; exists i; split; [ apply in_seq; lia | ].
          apply andb_true_intro; split;
            [ apply Nat.ltb_lt; lia | apply Nat.eqb_eq; symmetry; exact Hij ]. }
        rewrite E in H; discriminate. }
    assert (Hnd : NoDup (map (orbit p x) (seq 0 p)))
      by (apply NoDup_map_inj; [ exact Hinj | apply seq_NoDup ]).
    assert (Hincl : incl (map (orbit p x) (seq 0 p)) (seq 1 (p - 1))).
    { intros v Hv; apply in_map_iff in Hv as [k [Hk _]]; rewrite <- Hk.
      pose proof (orbit_unit p x k Hp Hx); apply in_seq; lia. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite length_map, !length_seq in Hlen; lia. }
  unfold has_coll in Hcoll.
  apply existsb_exists in Hcoll as [i [Hi Hinner]].
  apply existsb_exists in Hinner as [j [Hj Hterm]].
  apply andb_prop in Hterm as [Hlt Heq].
  apply Nat.ltb_lt in Hlt; apply Nat.eqb_eq in Heq; apply in_seq in Hj.
  exists i, j; repeat split; [ exact Hlt | lia | exact Heq ].
Qed.

(* EVENTUAL PERIODICITY: after index i, the orbit is periodic with period d>=1 *)
Theorem orbit_eventually_periodic : forall p x, prime (Z.of_nat p) -> 1 <= x <= p - 1 ->
  exists i d, 1 <= d /\ forall e, orbit p x (i + e + d) = orbit p x (i + e).
Proof.
  intros p x Hp Hx.
  destruct (orbit_collision p x Hp Hx) as [i [j [Hlt [_ Hij]]]].
  exists i, (j - i); split; [ lia | ].
  intro e.
  replace (i + e + (j - i)) with (j + e) by lia.
  symmetry; apply orbit_shift; exact Hij.
Qed.

(* ================================================================= *)
(*  §6  DISCRETE-LOG LINEARISATION OF ONE STEP  (reuse dlog_triad)    *)
(* ================================================================= *)

(* against a primitive root g, one self-power step is "scale the log by x":
   dlog(x^x) = x * dlog(x) (mod p-1).  Note the log-space orbit
   L |-> (x*L) mod (p-1) is NONLINEAR, since x = pw p g L depends on L. *)
Lemma orbit_dlog_step : forall p g x,
  prime (Z.of_nat p) -> 1 <= g <= p - 1 -> ord p g = p - 1 -> 1 <= x <= p - 1 ->
  dlog p g (selfpow p x) = (dlog p g x * x) mod (p - 1).
Proof.
  intros p g x Hp Hg Hord Hx.
  destruct (dlog_triad p g x Hp Hg Hord Hx) as [_ [_ Hsp]]; exact Hsp.
Qed.

(* ----------------------------------------------------------------- *)
(*  MASTER: the careful self-power dynamics on F_p*                   *)
(* ----------------------------------------------------------------- *)

Theorem self_power_dynamics : forall p, prime (Z.of_nat p) ->
  (* exponent reduces mod p-1, base stays x *)
     (forall x, 1 <= x <= p - 1 -> selfpow p x = pw p x (x mod (p - 1)))
  (* the map stays on the units *)
  /\ (forall x, 1 <= x <= p - 1 -> 1 <= selfpow p x <= p - 1)
  (* boundary / distinguished points *)
  /\ selfpow p 0 = 1 /\ selfpow p 1 = 1 /\ selfpow p (p - 1) = 1
  (* fixed points characterised by the order *)
  /\ (forall x, 1 <= x <= p - 1 -> (selfpow p x = x <-> Nat.divide (ord p x) (x - 1)))
  (* every orbit is eventually periodic *)
  /\ (forall x, 1 <= x <= p - 1 ->
        exists i d, 1 <= d /\ forall e, orbit p x (i + e + d) = orbit p x (i + e)).
Proof.
  intros p Hp; assert (Hp2 : 2 <= p) by (destruct Hp; lia).
  split; [ intros x Hx; apply selfpow_exp_reduce; assumption | ].
  split; [ intros x Hx; apply selfpow_unit; assumption | ].
  split; [ apply selfpow_0; exact Hp2 | ].
  split; [ apply selfpow_1; exact Hp2 | ].
  split; [ apply selfpow_pm1; exact Hp | ].
  split; [ intros x Hx; apply selfpow_fixed_ord; assumption | ].
  intros x Hx; apply orbit_eventually_periodic; assumption.
Qed.

Print Assumptions self_power_dynamics.

(* ================================================================= *)
(*  END SelfPowerDynamics.v                                          *)
(*  The self-power map x |-> x^x mod p as a dynamical system on F_p*:  *)
(*  exponent reduction (base/exponent asymmetry), unit-closure,        *)
(*  boundary (0,1,p-1 all -> 1), fixed points (ord(x) | x-1), and      *)
(*  eventual periodicity of every orbit (pigeonhole on the p-1 units). *)
(*  One step linearises in discrete-log space to scaling by x.  Closed *)
(*  under the global context.                                         *)
(* ================================================================= *)
