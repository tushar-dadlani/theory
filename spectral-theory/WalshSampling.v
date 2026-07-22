(* ================================================================= *)
(*  WalshSampling.v                                                  *)
(*                                                                    *)
(*  THE FINITE SAMPLING THEOREM (discrete Shannon-Nyquist) on F_2^3,   *)
(*  and the bridge it exposes to the discrete contour integral.      *)
(*                                                                    *)
(*  Built on WalshHadamard.v -- the genuine Fourier transform on the   *)
(*  Boolean cube (shift theorem WH_shift, convolution theorem WH_conv, *)
(*  inversion WH_involution : H^2 = 8 I).  Here we add the SAMPLING     *)
(*  layer for the index-2 subgroup                                    *)
(*     H       = { x : c2 x = false }        (a hyperplane, |H| = 4)    *)
(*     H^perp  = { y : c0 y = c1 y = false } (its annihilator, |=2)     *)
(*                                                                    *)
(*    - WH_comb : WH 1_H = |H| * 1_{H^perp}   (the discrete Dirac comb; *)
(*        an indicator of a subgroup transforms to the indicator of     *)
(*        its annihilator -- the mechanism of ALL sampling theory);     *)
(*    - poisson_summation : 2 * (sum over H of f) = sum over H^perp of   *)
(*        WH f  (finite Poisson summation);                            *)
(*    - bandlimited_reconstruction : if WH f is supported off the       *)
(*        c2-axis (f is band-limited to a transversal of H^perp),     *)
(*        then f is constant along H-cosets, i.e. f is DETERMINED by     *)
(*        its 4 samples on H.  This is the discrete Nyquist criterion:   *)
(*        #samples (=|H|=4) = bandwidth, and undersampling would alias.  *)
(*                                                                    *)
(*  THE BRIDGE.  Poisson summation is not just the sampling mechanism;  *)
(*  it is the SAME identity that, in the continuous limit, yields the    *)
(*  functional equation of the theta function and hence of zeta -- the   *)
(*  s <-> 1-s reflection that the CONTOUR INTEGRAL exploits when shifting *)
(*  the Perron line.  Likewise WH_involution (recover f from WH f) and   *)
(*  bandlimited_reconstruction (recover f from its samples) are the       *)
(*  FINITE instances of Fourier/Mellin INVERSION -- exactly the move       *)
(*  Perron contour performs (recover a summatory function from its       *)
(*  Dirichlet series).  The arithmetic-side cousin already in the repo    *)
(*  is PosetMobiusFTC (Mobius inversion = a discrete fundamental theorem   *)
(*  of calculus).  So this file makes the harmonic-duality / inversion     *)
(*  principle -- shared by sampling, Poisson summation, Mobius inversion,  *)
(*  and Perron formula -- concrete and machine-checked in the one        *)
(*  setting where it needs no complex analysis: the self-dual finite       *)
(*  group F_2^3.  (No rigorous WH -> zeta theorem is claimed; the bridge   *)
(*  is the common inversion structure, provable here, out of reach for      *)
(*  zeta without the contour.)                                            *)
(*                                                                    *)
(*  Axiom-free: pure Z arithmetic on a finite group (Closed under the *)
(*  global context).                                                 *)
(* ================================================================= *)

Require Import WalshHadamard.
From Stdlib Require Import ZArith List Bool Lia Ring.
Import ListNotations.
Open Scope Z_scope.

(* projection onto the sampling hyperplane H (zero the c2 coordinate) *)
Definition proj (x : P3) : P3 := mkP (c0 x) (c1 x) false.

(* indicator of the subgroup H = {c2 = false} and its annihilator *)
Definition indH : Signal := fun x => if c2 x then 0 else 1.
Definition indHperp : Signal := fun y => if orb (c0 y) (c1 y) then 0 else 1.

(* the two combs: sums over H and over H^perp *)
Definition sumH (f : Signal) : Z := fold_right Z.add 0 (map (fun x => indH x * f x) allP).
Definition sumHperp (g : Signal) : Z := fold_right Z.add 0 (map (fun y => indHperp y * g y) allP).

(* ----------------------------------------------------------------- *)
(*  THE COMB TRANSFORM: WH 1_H = |H| * 1_{H^perp}                     *)
(* ----------------------------------------------------------------- *)

Theorem WH_comb : forall y, WH indH y = 4 * indHperp y.
Proof.
  intros [y0 y1 y2]; destruct y0, y1, y2; vm_compute; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  FINITE POISSON SUMMATION                                         *)
(* ----------------------------------------------------------------- *)

Theorem poisson_summation : forall f, 2 * sumH f = sumHperp (WH f).
Proof.
  intro f;
  cbv [sumH sumHperp WH indH indHperp allP chi dot signb c0 c1 c2
        andb orb xorb negb map fold_right]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  THE SAMPLING / NYQUIST RECONSTRUCTION                            *)
(* ----------------------------------------------------------------- *)

(* the character is unchanged by the projection when the frequency is  *)
(* off the c2-axis (c2 y = false) *)
Lemma dot_proj : forall z x, c2 z = false -> dot z x = dot z (proj x).
Proof.
  intros [z0 z1 z2] [x0 x1 x2] Hz; simpl in Hz; subst z2; reflexivity.
Qed.

Lemma chi_proj : forall z x, c2 z = false -> chi z x = chi z (proj x).
Proof. intros z x Hz; unfold chi; rewrite (dot_proj z x Hz); reflexivity. Qed.

(* a band-limited transform is invariant under projecting the argument *)
Lemma WH_proj : forall g x,
  (forall z, c2 z = true -> g z = 0) -> WH g x = WH g (proj x).
Proof.
  intros g x Hbl; unfold WH; f_equal; apply map_ext_in; intros z _.
  destruct (c2 z) eqn:E; [ rewrite (Hbl z E); ring | rewrite (chi_proj z x E); reflexivity ].
Qed.

(* DISCRETE NYQUIST: a signal band-limited off the c2-axis is constant  *)
(* along H-cosets, hence reconstructed from its 4 samples on H.         *)
Theorem bandlimited_reconstruction : forall f,
  (forall y, c2 y = true -> WH f y = 0) ->
  forall x, f x = f (proj x).
Proof.
  intros f Hbl x.
  assert (H8 : 8 * f x = 8 * f (proj x)).
  { rewrite <- (WH_involution f x), (WH_proj (WH f) x Hbl), (WH_involution f (proj x));
      reflexivity. }
  lia.
Qed.

Print Assumptions bandlimited_reconstruction.

(* ================================================================= *)
(*  END WalshSampling.v                                              *)
(*  The finite Shannon-Nyquist sampling theorem on F_2^3: the comb     *)
(*  transform WH 1_H = |H| 1_{H^perp}, Poisson summation, and the       *)
(*  band-limited reconstruction (4 samples <-> 4-band signal).  These   *)
(*  are the finite, complex-analysis-free instances of the Poisson-      *)
(*  summation / Fourier-inversion principle whose infinite forms give    *)
(*  the zeta functional equation and Perron contour formula.            *)
(*  ZERO Admitted; Closed under the global context.                    *)
(* ================================================================= *)
