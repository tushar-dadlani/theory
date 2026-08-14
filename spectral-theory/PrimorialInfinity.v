(* ================================================================= *)
(*  PrimorialInfinity.v                                              *)
(*                                                                    *)
(*  (primorial)^oo AS A FIRST-CLASS OBJECT, unifying its three faces:  *)
(*                                                                    *)
(*    (i)   the ORDER top    infty : InvLim         (omega+1)          *)
(*    (ii)  the RING point   Wzero : Zhat           (0 in Zhat=prod Zp)*)
(*    (iii) the ARCHIMEDEAN value  |n|_oo = 1/fabs   (reciprocal of the *)
(*          finite p-adic product)                                     *)
(*                                                                    *)
(*  packaged as `Record PrimInf` with a coherence field certifying     *)
(*  that the order-top and the ring point agree in every completion    *)
(*  Z_p (both are p^oo = 0), plus the archimedean reciprocal.  The      *)
(*  canonical inhabitant `primorial_infinity` is the statement         *)
(*     "(primorial)^oo is the order-top, is 0 in every Z_p, and is       *)
(*      1/prod_p |.|_p at infinity".                                   *)
(*  Payoff: `adele_split` states A_Q = R x A_f at a rational point.     *)
(*                                                                    *)
(*  Axiom-free (nat / Z / Q).                                         *)
(* ================================================================= *)

From Stdlib Require Import Arith Lia ZArith QArith.
Require Import PadicIntegers InvLimit ChainTower ProfiniteInteger ProfiniteBridge
        ProductFormulaQ ArchimedeanTower PrimeFactorizationN.

Local Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  Face (iii): the archimedean value is the reciprocal of the finite  *)
(*  p-adic product -- pure repackaging of archimedean_reconstruct.     *)
(* ----------------------------------------------------------------- *)
Lemma arch_is_recip_finite : forall n B, 0 < n -> n <= Z.of_nat B ->
  exists ks, code (primes_upto B) ks = n
    /\ (inject_Z n == / fabs (primes_upto B) ks)%Q
    /\ (inject_Z n * fabs (primes_upto B) ks == 1)%Q.
Proof.
  intros n B Hn HB.
  destruct (archimedean_reconstruct n B Hn HB) as [ks [_ [Hc [Hpf Hrec]]]].
  exists ks; split; [ exact Hc | split; [ exact Hrec | exact Hpf ] ].
Qed.

(* ================================================================= *)
(*  The unified object                                               *)
(* ================================================================= *)

Record PrimInf := {
  (* face (i): the order omega+1 *)
  pi_order      : InvLim;
  pi_order_top  : forall X, leL X pi_order;
  (* face (ii): the point in the profinite ring Zhat = prod_p Z_p *)
  pi_ring       : Zhat;
  (* (i)<->(ii): order-top and ring point agree in every completion Z_p *)
  pi_bridge     : forall p (Hp : (2 <= p)%nat) k,
      projZ p k (compW p Hp pi_ring) = projZ p k (Phi p Hp pi_order);
  (* face (iii): archimedean value = reciprocal of the finite product *)
  pi_arch       : forall n B, 0 < n -> n <= Z.of_nat B -> exists ks,
      code (primes_upto B) ks = n
      /\ (inject_Z n == / fabs (primes_upto B) ks)%Q
      /\ (inject_Z n * fabs (primes_upto B) ks == 1)%Q
}.

(* the canonical inhabitant: (primorial)^oo *)
Definition primorial_infinity : PrimInf :=
  {| pi_order      := infty;
     pi_order_top  := infty_top;
     pi_ring       := Wzero;
     pi_bridge     := fun p Hp k =>
        eq_trans (compW_Wzero p Hp k) (eq_sym (Phi_infty p Hp k));
     pi_arch       := arch_is_recip_finite |}.

(* ----------------------------------------------------------------- *)
(*  MASTER THEOREM: the three faces cohere                           *)
(* ----------------------------------------------------------------- *)
Theorem primorial_infinity_coheres :
  (* (i) the order face: infty is the top of omega+1 *)
  (forall X, leL X (pi_order primorial_infinity))
  (* (i)<->(ii): order-top and ring point agree in every Z_p *)
  /\ (forall p (Hp : (2 <= p)%nat) k,
        projZ p k (compW p Hp (pi_ring primorial_infinity))
        = projZ p k (Phi p Hp (pi_order primorial_infinity)))
  (* (ii): the canonical infinite primorial is 0 in every completion Z_p *)
  /\ (forall p (Hp : (2 <= p)%nat) k,
        projZ p k (compW p Hp (pi_ring primorial_infinity)) = projZ p k (Zzero p))
  (* (ii)<->(iii): archimedean value = reciprocal of the finite product *)
  /\ (forall n B, 0 < n -> n <= Z.of_nat B -> exists ks,
        code (primes_upto B) ks = n
        /\ (inject_Z n == / fabs (primes_upto B) ks)%Q
        /\ (inject_Z n * fabs (primes_upto B) ks == 1)%Q).
Proof.
  split; [ exact (pi_order_top primorial_infinity) | ].
  split; [ exact (pi_bridge primorial_infinity) | ].
  split; [ exact (fun p Hp k => compW_Wzero p Hp k) | ].
  exact (pi_arch primorial_infinity).
Qed.

Print Assumptions primorial_infinity_coheres.

(* ================================================================= *)
(*  PAYOFF: the adele split  A_Q = R x A_f  at a rational point       *)
(*  R-factor = archimedean size |n|_oo (face iii);                     *)
(*  A_f-factor = finite p-adic product fabs (face ii);                 *)
(*  glued by the product formula |n|_oo . prod_p |n|_p = 1.            *)
(* ================================================================= *)
Corollary adele_split : forall n, 0 < n ->
  exists arch ringf : Q,
       (arch == inject_Z n)%Q
    /\ (exists B ks, code (primes_upto B) ks = n /\ (ringf == fabs (primes_upto B) ks)%Q)
    /\ (arch * ringf == 1)%Q.
Proof.
  intros n Hn.
  set (B := Z.to_nat n).
  assert (HB : n <= Z.of_nat B) by (unfold B; rewrite Z2Nat.id; lia).
  destruct (arch_is_recip_finite n B Hn HB) as [ks [Hc [_ Hpf]]].
  exists (inject_Z n), (fabs (primes_upto B) ks).
  split; [ reflexivity | ].
  split; [ exists B, ks; split; [ exact Hc | reflexivity ] | exact Hpf ].
Qed.

Print Assumptions adele_split.

(* ================================================================= *)
(*  END PrimorialInfinity.v                                          *)
(*  (primorial)^oo as one object: order-top = 0-in-every-Z_p =         *)
(*  1/prod|.|_p, with the adele split A_Q = R x A_f as the payoff.      *)
(* ================================================================= *)
