(* ================================================================= *)
(*  QuadraticGaussSum.v                                              *)
(*                                                                    *)
(*  THE QUADRATIC GAUSS SUM and its SQUARE:  g^2 = chi(-1) * p.        *)
(*                                                                    *)
(*  For an ODD prime p and a primitive root g, take the QUADRATIC      *)
(*  (Legendre) character                                              *)
(*                                                                    *)
(*      chi = dchar p g ((p-1)/2)                                     *)
(*                                                                    *)
(*  the order-2 Dirichlet character (+1 on residues, -1 on non-       *)
(*  residues).  Its Gauss sum  g = sum_{n=1}^{p-1} chi(n) zeta^n       *)
(*  satisfies                                                         *)
(*                                                                    *)
(*      g^2 = chi(-1) * p    (= +p  or  -p).                          *)
(*                                                                    *)
(*  GaussSum.v already proved |g|^2 = g * conj(g) = p for EVERY        *)
(*  nonprincipal character; the quadratic case is that instance with  *)
(*  a0 = (p-1)/2.  The NEW content here is the value of g^2 (its       *)
(*  sign), obtained from |g|^2 = p together with the reflection        *)
(*  identity  conj(g) = chi(-1) * g, which holds because the           *)
(*  quadratic character is REAL-valued.  Combining:                    *)
(*      p = g * conj(g) = chi(-1) * g^2   =>   g^2 = chi(-1) * p.      *)
(*  Since chi(-1) is real of modulus 1 it is +/- 1, so g^2 = +/- p.    *)
(*                                                                    *)
(*  (Determining WHICH sign -- chi(-1) = (-1)^((p-1)/2), i.e. +p for   *)
(*  p = 1 mod 4 and -p for p = 3 mod 4 -- needs g^((p-1)/2) = -1 and   *)
(*  is left for future work; the +/- dichotomy is proved here.)       *)
(*                                                                    *)
(*  Uses the classical Reals axioms (quarantined, via w / trig), like  *)
(*  the whole character layer.                                        *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia List Bool Permutation Reals Lra.
Require Import ZmodPStar ZmodOrder PrimitiveRoot DirichletModP DirichletLEuler
        ComplexField RootsOfUnity DFTInversion DFTConvolution CharactersModN GaussSum.
Import ListNotations.
Open Scope nat_scope.

(* ================================================================= *)
(*  §0  a real power of w:  w^k = conj(w^k) whenever w^(2k) = 1        *)
(* ================================================================= *)

(* If (w N)^k squares to 1 then it equals its own conjugate, i.e.      *)
(* wc^k = w^k.  Pure roots-of-unity algebra; used to prove that the    *)
(* quadratic character is real-valued.                                *)
Lemma pow_real_eq : forall N k,
  Cpow (w N) (k + k) = C1 -> Cpow (wc N) k = Cpow (w N) k.
Proof.
  intros N k H.
  assert (HBA : Cmul (Cpow (wc N) k) (Cpow (w N) k) = C1)
    by (rewrite <- Cpow_Cmul, wc_w_1, Cpow_C1; reflexivity).
  assert (HAA : Cmul (Cpow (w N) k) (Cpow (w N) k) = C1)
    by (rewrite <- Cpow_add; exact H).
  transitivity (Cmul (Cpow (wc N) k) (Cmul (Cpow (w N) k) (Cpow (w N) k))).
  - rewrite HAA; ring.
  - replace (Cmul (Cpow (wc N) k) (Cmul (Cpow (w N) k) (Cpow (w N) k)))
      with (Cmul (Cmul (Cpow (wc N) k) (Cpow (w N) k)) (Cpow (w N) k)) by ring.
    rewrite HBA; ring.
Qed.

(* ================================================================= *)
(*  The quadratic character mod an odd prime p                        *)
(* ================================================================= *)

Section QuadGauss.

Variable p : nat.
Hypothesis Hp : prime (Z.of_nat p).
Variable g : nat.
Hypothesis Hg : 1 <= g <= p - 1.
Hypothesis Hord : ord p g = p - 1.
Variable a0 : nat.
Hypothesis Ha0 : 0 < a0 < p - 1.
Hypothesis Hhalf : 2 * a0 = p - 1.            (* a0 = (p-1)/2 : the quadratic char *)

Lemma Hp2 : 2 <= p.        Proof. destruct Hp as [Hgt _]; lia. Qed.
Lemma H0p : 0 < p.         Proof. pose proof Hp2; lia. Qed.
Lemma H0p1 : 0 < p - 1.    Proof. pose proof Hp2; lia. Qed.

Notation chi := (dchar p g a0).

(* ----------------------------------------------------------------- *)
(*  §1  chi is REAL-valued:  conj(chi n) = chi n                       *)
(* ----------------------------------------------------------------- *)

Lemma chi_real : forall n, Cconj (chi n) = chi n.
Proof.
  intro n; unfold dchar.
  destruct (n mod p =? 0) eqn:E.
  - apply Ceq; simpl; ring.
  - set (d := dlog p g (n mod p)).
    rewrite conj_w_pow.
    apply pow_real_eq.
    replace (a0 * d + a0 * d) with (2 * a0 * d) by ring.
    rewrite Hhalf, Cpow_mul, w_pow_N by (apply H0p1).
    apply Cpow_C1.
Qed.

(* chi(-1)^2 = 1 : chi(-1) is real of modulus 1 *)
Lemma chi_neg1_sq : Cmul (chi (p - 1)) (chi (p - 1)) = C1.
Proof.
  rewrite <- (chi_real (p - 1)) at 2.
  apply (chi_norm1 p g Hg Hord a0 Ha0 (p - 1)); pose proof Hp2; lia.
Qed.

(* chi(-1) = +1 or -1 *)
Lemma chi_neg1_cases : chi (p - 1) = C1 \/ chi (p - 1) = Copp C1.
Proof.
  pose proof (chi_real (p - 1)) as Hre.
  pose proof (chi_norm1 p g Hg Hord a0 Ha0 (p - 1) ltac:(pose proof Hp2; lia)) as Hn.
  destruct (chi (p - 1)) as [a b] eqn:Ez.
  (* imaginary part is 0 *)
  assert (Hb : b = 0%R).
  { apply (f_equal Im) in Hre; simpl in Hre; lra. }
  (* a^2 = 1 *)
  assert (Ha : (a * a + b * b = 1)%R).
  { rewrite Cmul_conj in Hn. apply (f_equal Re) in Hn.
    unfold Cnorm2, RtoC in Hn; simpl in Hn; lra. }
  assert (Haa : (a = 1 \/ a = -1)%R).
  { assert (H0 : ((a - 1) * (a + 1) = 0)%R) by nra.
    apply Rmult_integral in H0; destruct H0; [left|right]; lra. }
  destruct Haa as [-> | ->]; [left | right]; apply Ceq; simpl; lra.
Qed.

(* ----------------------------------------------------------------- *)
(*  §2  the reflection on additive roots:  wc^((p-1)x mod p) = w^x     *)
(* ----------------------------------------------------------------- *)

(* w^((p-1)x) is the inverse of w^x, hence its conjugate; conjugating   *)
(* back gives w^x.                                                     *)
Lemma w_pow_pm1 : forall x, 1 <= x <= p - 1 ->
  Cpow (w p) ((p - 1) * x) = Cconj (Cpow (w p) x).
Proof.
  intros x Hx.
  assert (Hinv1 : Cmul (Cpow (w p) ((p - 1) * x)) (Cpow (w p) x) = C1).
  { rewrite <- Cpow_add.
    replace ((p - 1) * x + x) with (p * x) by (pose proof Hp2; nia).
    rewrite Cpow_mul, w_pow_N by (apply H0p); apply Cpow_C1. }
  assert (Hinv2 : Cmul (Cpow (w p) x) (Cconj (Cpow (w p) x)) = C1).
  { rewrite Cmul_conj, (Cnorm2_pow (w p) x (Cnorm2_w p)); reflexivity. }
  (* both are the inverse of (w p)^x *)
  transitivity (Cmul (Cpow (w p) ((p - 1) * x))
                     (Cmul (Cpow (w p) x) (Cconj (Cpow (w p) x)))).
  - rewrite Hinv2; ring.
  - replace (Cmul (Cpow (w p) ((p - 1) * x))
                  (Cmul (Cpow (w p) x) (Cconj (Cpow (w p) x))))
      with (Cmul (Cmul (Cpow (w p) ((p - 1) * x)) (Cpow (w p) x))
                 (Cconj (Cpow (w p) x))) by ring.
    rewrite Hinv1; ring.
Qed.

Lemma wc_reindex : forall x, 1 <= x <= p - 1 ->
  Cpow (wc p) ((p - 1) * x mod p) = Cpow (w p) x.
Proof.
  intros x Hx.
  rewrite <- conj_w_pow, <- (Cpow_w_mod p ((p - 1) * x) (H0p)).
  rewrite (w_pow_pm1 x Hx), Cconj_involutive; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  §3  the reflection identity:  conj(g) = chi(-1) * g               *)
(* ----------------------------------------------------------------- *)

Lemma gauss_conj_chi :
  Cconj (gauss p g a0) = Cmul (chi (p - 1)) (gauss p g a0).
Proof.
  rewrite gauss_conj_eq.
  (* replace conj(chi b) by chi b (chi real) *)
  rewrite (Sf_ext (fun b => Cmul (Cconj (chi b)) (Cpow (wc p) b))
                  (fun b => Cmul (chi b) (Cpow (wc p) b)) (seq 1 (p - 1)))
    by (intros b _; rewrite chi_real; reflexivity).
  (* reindex b -> (p-1)*b mod p *)
  assert (Hnd : ~ Nat.divide p (p - 1)) by (apply unit_not_div; pose proof Hp2; lia).
  rewrite (Sf_reindex_mul (fun b => Cmul (chi b) (Cpow (wc p) b)) (p - 1) p Hp Hnd).
  (* each term becomes chi(-1) * (chi x * w^x) *)
  rewrite (Sf_ext
             (fun x => Cmul (chi ((p - 1) * x mod p)) (Cpow (wc p) ((p - 1) * x mod p)))
             (fun x => Cmul (chi (p - 1)) (Cmul (chi x) (Cpow (w p) x)))
             (seq 1 (p - 1))).
  - rewrite Sf_scale_l; reflexivity.
  - intros x Hx; apply in_seq in Hx.
    rewrite chi_mod, (dchar_mul p g a0 (p - 1) x Hp Hg Hord).
    rewrite (wc_reindex x ltac:(lia)); ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  §4  the square:  g^2 = chi(-1) * p                                 *)
(* ----------------------------------------------------------------- *)

Lemma gauss_sq :
  Cmul (gauss p g a0) (gauss p g a0) = Cmul (chi (p - 1)) (RtoC (INR p)).
Proof.
  pose proof (gauss_abs p Hp g Hg Hord a0 Ha0) as Habs.
  rewrite gauss_conj_chi in Habs.
  (* Habs : g * (chi(-1) * g) = p ; rearrange to chi(-1) * (g*g) = p *)
  assert (Hstep : Cmul (chi (p - 1)) (Cmul (gauss p g a0) (gauss p g a0))
                  = RtoC (INR p)) by (rewrite <- Habs; ring).
  pose proof chi_neg1_sq as HX2.
  (* g*g = (chi(-1)*chi(-1)) * (g*g) = chi(-1) * (chi(-1)*(g*g)) = chi(-1)*p *)
  transitivity (Cmul (Cmul (chi (p - 1)) (chi (p - 1)))
                     (Cmul (gauss p g a0) (gauss p g a0))).
  - rewrite HX2; ring.
  - replace (Cmul (Cmul (chi (p - 1)) (chi (p - 1)))
                  (Cmul (gauss p g a0) (gauss p g a0)))
      with (Cmul (chi (p - 1))
                 (Cmul (chi (p - 1)) (Cmul (gauss p g a0) (gauss p g a0)))) by ring.
    rewrite Hstep; reflexivity.
Qed.

End QuadGauss.

(* ================================================================= *)
(*  MASTER: the quadratic Gauss sum squares to +/- p                  *)
(* ================================================================= *)

Theorem quadratic_gauss_sum_sq :
  forall p, prime (Z.of_nat p) -> (p mod 2 = 1)%nat ->
  exists g, 1 <= g <= p - 1 /\ ord p g = p - 1 /\
    (* g^2 = chi(-1) * p, and chi(-1) = +/- 1, hence g^2 = +/- p *)
    Cmul (gauss p g ((p - 1) / 2)) (gauss p g ((p - 1) / 2))
      = Cmul (dchar p g ((p - 1) / 2) (p - 1)) (RtoC (INR p)) /\
    (dchar p g ((p - 1) / 2) (p - 1) = C1 \/
     dchar p g ((p - 1) / 2) (p - 1) = Copp C1) /\
    (Cmul (gauss p g ((p - 1) / 2)) (gauss p g ((p - 1) / 2)) = RtoC (INR p) \/
     Cmul (gauss p g ((p - 1) / 2)) (gauss p g ((p - 1) / 2)) = Copp (RtoC (INR p))).
Proof.
  intros p Hp Hodd.
  assert (Hp2 : 2 <= p) by (destruct Hp as [Hgt _]; lia).
  (* p is odd => p >= 3 *)
  assert (Hp3 : 3 <= p).
  { destruct (Nat.eq_dec p 2) as [->|Hne]; [ discriminate Hodd | lia ]. }
  set (a0 := (p - 1) / 2).
  pose proof (Nat.div_mod_eq (p - 1) 2).
  pose proof (Nat.div_mod_eq p 2).
  pose proof (Nat.mod_upper_bound (p - 1) 2).
  pose proof (Nat.mod_upper_bound p 2).
  assert (Hhalf : 2 * a0 = p - 1) by (unfold a0; lia).
  assert (Ha0 : 0 < a0 < p - 1) by (unfold a0; lia).
  destruct (units_cyclic p Hp) as [g [Hg Hord]].
  exists g; repeat split; [ lia | lia | exact Hord | | | ].
  - exact (gauss_sq p Hp g Hg Hord a0 Ha0 Hhalf).
  - exact (chi_neg1_cases p Hp g Hg Hord a0 Ha0 Hhalf).
  - destruct (chi_neg1_cases p Hp g Hg Hord a0 Ha0 Hhalf) as [E|E];
      rewrite (gauss_sq p Hp g Hg Hord a0 Ha0 Hhalf), E.
    + left; ring.
    + right; ring.
Qed.

Print Assumptions quadratic_gauss_sum_sq.

(* ================================================================= *)
(*  END QuadraticGaussSum.v                                          *)
(*  The quadratic (Legendre) Gauss sum g = sum chi(n) zeta^n for the   *)
(*  order-2 character chi = dchar p g ((p-1)/2) mod an odd prime p     *)
(*  squares to chi(-1)*p = +/- p.  Proof: GaussSum's |g|^2 = p plus    *)
(*  the reflection conj(g) = chi(-1)*g (chi is real-valued), so        *)
(*  p = g*conj(g) = chi(-1)*g^2.  Uses the classical Reals axioms      *)
(*  (quarantined, via w/trig).                                        *)
(* ================================================================= *)
