(* ================================================================= *)
(*  PrimeDivisorPhi.v                                                *)
(*                                                                    *)
(*  THE PRIMITIVE-DIVISOR / PRIMITIVITY LEMMA.                        *)
(*                                                                    *)
(*  If a prime q divides Φ_n(a) but q ∤ n, then a is a *primitive*    *)
(*  n-th root mod q: q ∤ a^d − 1 for every proper divisor d of n.     *)
(*                                                                    *)
(*  Proof (double-root argument, all over ℤ, no F_q[X] needed):       *)
(*  suppose q ∣ a^d − 1 for a proper d ∣ n.  Then a^d − 1 =           *)
(*  ∏_{e∣d}Φ_e(a), so q ∣ Φ_e(a) for some proper divisor e of n.     *)
(*  Now q divides the two DISTINCT factors Φ_e(a), Φ_n(a) of          *)
(*  X^n−1 = Φ_n·(∏_{d<n}Φ_d).  Differentiating that factorisation     *)
(*  (product rule), every term of (X^n−1)′(a) carries a factor        *)
(*  Φ_e(a) or Φ_n(a), so q ∣ (X^n−1)′(a) = n·a^{n−1}.  Since q ∤ a,   *)
(*  q ∤ a^{n−1}, hence q ∣ n — contradiction.  AXIOM-FREE.           *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List.
Import ListNotations.
Require Import IntPoly PolyDiv IntPolyDeriv IntPolyDerivResp
        Cyclotomic CyclotomicProd.
Open Scope Z_scope.

(* ---- q dividing a cyclotomic factor divides the whole product ---- *)
Lemma eval_fold_in : forall a e l, In e l ->
  (eval (Phi e) a | eval (fold_right (fun d acc => pmul (Phi d) acc) [1%Z] l) a).
Proof.
  intros a e l; induction l as [|d l IH]; intro Hin; [ inversion Hin | ].
  cbn [fold_right]; rewrite eval_mul.
  destruct Hin as [->|Hin].
  - apply Z.divide_factor_l.
  - apply (Z.divide_trans _ _ _ (IH Hin)); apply Z.divide_factor_r.
Qed.

(* ---- a prime dividing the product divides one factor ---- *)
Lemma prime_dvd_fold : forall (q a : Z) l, prime q ->
  (q | eval (fold_right (fun d acc => pmul (Phi d) acc) [1%Z] l) a) ->
  exists e, In e l /\ (q | eval (Phi e) a).
Proof.
  intros q a l Hq; induction l as [|d l IH]; intro Hd.
  - exfalso; cbn [fold_right] in Hd.
    change (eval [1%Z] a) with (eval (pconst 1%Z) a) in Hd; rewrite eval_const in Hd.
    apply Z.divide_1_r in Hd.
    pose proof (prime_ge_2 _ Hq); destruct Hd; lia.
  - cbn [fold_right] in Hd; rewrite eval_mul in Hd.
    destruct (prime_mult q Hq _ _ Hd) as [H|H].
    + exists d; split; [ left; reflexivity | exact H ].
    + destruct (IH H) as [e [He Hqe]]; exists e; split; [ right; exact He | exact Hqe ].
Qed.

(* ---- q ∤ a  ⟹  q ∤ a^m  (prime q) ---- *)
Lemma prime_not_dvd_pow : forall (q a : Z) (m : nat),
  prime q -> ~ (q | a) -> ~ (q | a ^ Z.of_nat m).
Proof.
  intros q a m Hq Hqa; induction m as [|m IH]; intro Hd.
  - change (Z.of_nat 0) with 0%Z in Hd; rewrite Z.pow_0_r in Hd.
    apply Z.divide_1_r in Hd; pose proof (prime_ge_2 _ Hq); destruct Hd; lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hd by lia.
    destruct (prime_mult q Hq _ _ Hd) as [H|H]; [ apply Hqa; exact H | apply IH; exact H ].
Qed.

(* ---- q dividing two distinct factors ⟹ q ∣ (X^n−1)′(a) ---- *)
Lemma q_dvd_deriv_Xn1 : forall (q a : Z) (n e : nat),
  (1 <= n)%nat -> In e (properdivs n) ->
  (q | eval (Phi e) a) -> (q | eval (Phi n) a) ->
  (q | eval (pderiv (Xn1 n)) a).
Proof.
  intros q a n e Hn He HqE HqN.
  (* differentiate  X^n−1 = Φ_n · Dprod_n *)
  assert (Hfac : forall x, eval (Xn1 n) x = eval (pmul (Phi n) (Dprod n)) x).
  { intro x; rewrite eval_mul; apply (cyclotomic_prod_Z n Hn x). }
  rewrite (pderiv_resp_eval _ _ Hfac a), pderiv_mul_eval.
  apply Z.divide_add_r.
  - (* Φ_n′(a)·Dprod_n(a): e ∈ properdivs n ⟹ Φ_e(a) ∣ Dprod_n(a) *)
    apply Z.divide_mul_r.
    apply (Z.divide_trans _ _ _ HqE).
    unfold Dprod; apply (eval_fold_in a e (properdivs n) He).
  - (* Φ_n(a)·Dprod_n′(a) *)
    apply Z.divide_mul_l; exact HqN.
Qed.

(* ================================================================= *)
(*  THE PRIMITIVITY LEMMA (over ℤ).                                  *)
(* ================================================================= *)
Theorem phi_primitive : forall (q a : Z) (n : nat),
  prime q -> ~ (q | a) -> (1 <= n)%nat ->
  (q | eval (Phi n) a) -> ~ (q | Z.of_nat n) ->
  forall d, Nat.divide d n -> (d < n)%nat -> ~ (q | a ^ Z.of_nat d - 1).
Proof.
  intros q a n Hq Hqa Hn HqN HqnotN d Hd Hdlt Hcontra.
  (* d ≥ 1 *)
  assert (Hd1 : (1 <= d)%nat).
  { destruct d as [|d']; [ | lia ].
    destruct Hd as [k Hk]; simpl in Hk; lia. }
  (* q | a^d − 1 = Φ_d(a) · Dprod_d(a) *)
  assert (HqXd : (q | eval (Phi d) a * eval (Dprod d) a)).
  { rewrite <- (cyclotomic_prod_Z d Hd1 a), eval_Xn1; exact Hcontra. }
  (* extract a proper divisor e of n with q | Φ_e(a) *)
  assert (He : exists e, In e (properdivs n) /\ (q | eval (Phi e) a)).
  { destruct (prime_mult q Hq _ _ HqXd) as [H|H].
    - (* e := d itself *)
      exists d; split; [ apply in_properdivs_iff; repeat split; [exact Hd|exact Hd1|exact Hdlt] | exact H ].
    - (* q | Dprod_d(a) = fold over properdivs d *)
      unfold Dprod in H; destruct (prime_dvd_fold q a (properdivs d) Hq H) as [e [Hein Hqe]].
      apply in_properdivs_iff in Hein; destruct Hein as [Hed [He1 Hedlt]].
      exists e; split; [ | exact Hqe ].
      apply in_properdivs_iff; repeat split.
      + apply (Nat.divide_trans e d n Hed Hd).
      + exact He1.
      + lia. }
  destruct He as [e [Hein Hqe]].
  (* double-root: q | (X^n−1)′(a) = n · a^{n−1} *)
  pose proof (q_dvd_deriv_Xn1 q a n e Hn Hein Hqe HqN) as Hder.
  rewrite peval_pderiv_Xn1 in Hder.
  (* q ∤ a^{n−1}, so q | n : contradiction *)
  destruct (prime_mult q Hq _ _ Hder) as [H|H].
  - apply HqnotN; exact H.
  - apply (prime_not_dvd_pow q a (Nat.pred n) Hq Hqa); exact H.
Qed.

Print Assumptions phi_primitive.

(* ================================================================= *)
(*  END PrimeDivisorPhi.v                                            *)
(*  q ∣ Φ_n(a), q ∤ n  ⟹  a is a primitive n-th root mod q.          *)
(*  Closed under the global context (axiom-free).                    *)
(* ================================================================= *)
