(* ================================================================= *)
(*  FordCircles.v  —  the FORD-CIRCLE TANGENCY THEOREM (axiom-free).  *)
(*                                                                    *)
(*  The Ford circle at a reduced fraction p/q (q>0) is centred at     *)
(*  (p/q, 1/(2q²)) with radius 1/(2q²), tangent to the real axis.     *)
(*  For two of them the centre-distance collapses exactly:            *)
(*                                                                    *)
(*     dist² = (r₁+r₂)² + ((ad−bc)² − 1)/(b²d²)   (`ford_identity`)    *)
(*                                                                    *)
(*  so, since ad−bc is an integer:                                    *)
(*     • ad−bc = ±1  ⟺ Farey neighbours ⟹ externally TANGENT         *)
(*                                     (`ford_tangent`),               *)
(*     • ad ≠ bc (distinct fractions) ⟹ NEVER OVERLAP                 *)
(*                                     (`ford_no_overlap`),            *)
(*     • |ad−bc| ≥ 2 ⟹ strictly DISJOINT (`ford_disjoint`).           *)
(*  Bundled in `ford_circles`.  Everything over ℚ, so                 *)
(*  `Print Assumptions` = Closed under the global context — AXIOM-    *)
(*  FREE (no classical Reals): this is pure arithmetic.               *)
(*                                                                    *)
(*  This is the GEOMETRIC SUBSTRATE of the Farey / modular /          *)
(*  θ-function story (Ford circles are the horocycles at the cusps of *)
(*  PSL(2,ℤ)) — but it is NOT the analytic theta transformation       *)
(*  θ(1/t)=√t·θ(t) itself, which still needs Poisson/Fourier or       *)
(*  contour analysis.  It is the modular skeleton, honestly labelled. *)
(* ================================================================= *)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
Local Open Scope Q_scope.

(* Ford circle at reduced p/q (q>0): centre (p/q, 1/(2q^2)), radius 1/(2q^2). *)
Definition fx (a b : Z) : Q := inject_Z a / inject_Z b.
Definition fr (b : Z) : Q := 1 / (2 * (inject_Z b * inject_Z b)).
Definition dist_sq (a b c d : Z) : Q :=
  (fx a b - fx c d) * (fx a b - fx c d) + (fr b - fr d) * (fr b - fr d).
Definition radsum (b d : Z) : Q := fr b + fr d.

Lemma injZ_pos : forall b : Z, (0 < b)%Z -> 0 < inject_Z b.
Proof. intros b Hb; change 0 with (inject_Z 0); rewrite <- Zlt_Qlt; exact Hb. Qed.
Lemma injZ_nz : forall b : Z, (0 < b)%Z -> ~ inject_Z b == 0.
Proof. intros b Hb; apply Qnot_eq_sym, Qlt_not_eq, injZ_pos, Hb. Qed.

Lemma detQ : forall a b c d : Z,
  inject_Z a * inject_Z d - inject_Z b * inject_Z c == inject_Z (a * d - b * c).
Proof.
  intros a b c d. rewrite <- !inject_Z_mult. unfold Qminus.
  rewrite <- inject_Z_opp, <- inject_Z_plus.
  replace (a * d + - (b * c))%Z with (a * d - b * c)%Z by ring. reflexivity.
Qed.

(* the exact Ford identity:  dist^2 = (r1+r2)^2 + (det^2 - 1)/(b^2 d^2). *)
Theorem ford_identity : forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
  dist_sq a b c d ==
  radsum b d * radsum b d
  + (inject_Z (a * d - b * c) * inject_Z (a * d - b * c) - 1)
    / (inject_Z b * inject_Z b * (inject_Z d * inject_Z d)).
Proof.
  intros a b c d Hb Hd.
  assert (Hbz := injZ_nz b Hb). assert (Hdz := injZ_nz d Hd).
  rewrite <- !detQ. unfold dist_sq, radsum, fx, fr. field. split; assumption.
Qed.

Theorem ford_tangent : forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
  (a * d - b * c = 1)%Z \/ (a * d - b * c = -1)%Z ->
  dist_sq a b c d == radsum b d * radsum b d.
Proof.
  intros a b c d Hb Hd Hdet.
  rewrite (ford_identity a b c d Hb Hd).
  assert (Hz : (inject_Z (a * d - b * c) * inject_Z (a * d - b * c) - 1)
               / (inject_Z b * inject_Z b * (inject_Z d * inject_Z d)) == 0).
  { assert (Hn : inject_Z (a * d - b * c) * inject_Z (a * d - b * c) - 1 == 0).
    { rewrite <- inject_Z_mult.
      replace ((a * d - b * c) * (a * d - b * c))%Z with 1%Z by (destruct Hdet as [-> | ->]; ring).
      change (inject_Z 1) with 1; ring. }
    rewrite Hn; unfold Qdiv; ring. }
  rewrite Hz; ring.
Qed.

Theorem ford_no_overlap : forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
  (a * d <> b * c)%Z ->
  radsum b d * radsum b d <= dist_sq a b c d.
Proof.
  intros a b c d Hb Hd Hne.
  rewrite (ford_identity a b c d Hb Hd).
  set (D := inject_Z (a * d - b * c)).
  set (den := inject_Z b * inject_Z b * (inject_Z d * inject_Z d)).
  assert (Hden : 0 < den).
  { unfold den. pose proof (injZ_pos b Hb) as Hbp; pose proof (injZ_pos d Hd) as Hdp;
    apply Qmult_lt_0_compat; apply Qmult_lt_0_compat; assumption. }
  assert (HD2 : 1 <= D * D).
  { unfold D. rewrite <- inject_Z_mult. change 1 with (inject_Z 1).
    rewrite <- Zle_Qle. nia. }
  assert (Hfrac : 0 <= (D * D - 1) / den).
  { apply Qmult_le_0_compat; [ lra | apply Qlt_le_weak, Qinv_lt_0_compat, Hden ]. }
  lra.
Qed.

Theorem ford_disjoint : forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
  (2 <= Z.abs (a * d - b * c))%Z ->
  radsum b d * radsum b d < dist_sq a b c d.
Proof.
  intros a b c d Hb Hd Hdet.
  rewrite (ford_identity a b c d Hb Hd).
  set (D := inject_Z (a * d - b * c)).
  set (den := inject_Z b * inject_Z b * (inject_Z d * inject_Z d)).
  assert (Hden : 0 < den).
  { unfold den. pose proof (injZ_pos b Hb) as Hbp; pose proof (injZ_pos d Hd) as Hdp;
    apply Qmult_lt_0_compat; apply Qmult_lt_0_compat; assumption. }
  assert (HD2 : 4 <= D * D).
  { unfold D. rewrite <- inject_Z_mult. change 4 with (inject_Z 4).
    rewrite <- Zle_Qle. nia. }
  assert (Hfrac : 0 < (D * D - 1) / den).
  { unfold Qdiv; apply Qmult_lt_0_compat; [ lra | apply Qinv_lt_0_compat, Hden ]. }
  lra.
Qed.

(* master: the Ford-circle tangency theorem *)
Theorem ford_circles :
  (forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
     dist_sq a b c d == radsum b d * radsum b d
     + (inject_Z (a*d-b*c) * inject_Z (a*d-b*c) - 1)
       / (inject_Z b * inject_Z b * (inject_Z d * inject_Z d))) /\
  (forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
     (a*d-b*c = 1)%Z \/ (a*d-b*c = -1)%Z -> dist_sq a b c d == radsum b d * radsum b d) /\
  (forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
     (a*d <> b*c)%Z -> radsum b d * radsum b d <= dist_sq a b c d) /\
  (forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z ->
     (2 <= Z.abs (a*d-b*c))%Z -> radsum b d * radsum b d < dist_sq a b c d).
Proof.
  repeat split; [ exact ford_identity | exact ford_tangent | exact ford_no_overlap | exact ford_disjoint ].
Qed.
Print Assumptions ford_circles.

(* ================================================================= *)
(*  END FordCircles.v.  |ad−bc|≥1 ⟹ Ford circles don't overlap;      *)
(*  =1 ⟺ tangent ⟺ Farey neighbours.  Axiom-free.                    *)
(* ================================================================= *)
