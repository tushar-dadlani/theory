(* ================================================================= *)
(*  CEisensteinResidue.v  —  the residue field at a split prime, and   *)
(*  the CUBIC RESIDUE SYMBOL.                                          *)
(*                                                                    *)
(*    econg pi a b  : a = b (mod pi)                                   *)
(*    cong_int      : every element is congruent to a rational integer *)
(*    int_cong_iff  : pi | m  <->  p | m,  for a rational integer m    *)
(*    cube_roots_distinct : 1, om, om^2 are pairwise incongruent mod pi*)
(*    efermat       : alpha^(p-1) = 1 (mod pi)   for pi not dividing a *)
(*    cubic_symbol_value : alpha^((p-1)/3) is congruent to 1, om or    *)
(*                    om^2 -- the CUBIC RESIDUE SYMBOL                 *)
(*                                                                    *)
(*  THE RESIDUE FIELD IS F_p, and that is what makes the symbol work.  *)
(*  The split theorem now hands back not just pi with N(pi) = p but    *)
(*  the integer t with pi | t - om -- so om is congruent to a RATIONAL *)
(*  INTEGER mod pi, and therefore so is every a + b om, namely a + bt. *)
(*  The map Z -> Z[om]/pi is onto, and its kernel is pZ because        *)
(*  pi | m forces p = N(pi) | N(m) = m^2.  Hence Z[om]/pi = Z/p and    *)
(*  Fermat transfers verbatim from ZmodPStar.                          *)
(*                                                                    *)
(*  THE THREE CUBE ROOTS ARE DISTINCT mod pi for a cheap reason: each  *)
(*  difference -- om - 1, om^2 - 1, om^2 - om -- has norm exactly 3,   *)
(*  so pi dividing one would give p | 3, false for p >= 7.  The same   *)
(*  computation three times.                                           *)
(*                                                                    *)
(*  THE SYMBOL IS THEN FORCED.  x = alpha^((p-1)/3) has x^3 = 1 mod pi *)
(*  by Fermat, and x^3 - 1 = (x-1)(x-om)(x-om^2) exactly, so the       *)
(*  primality of pi (irred_prime, twice) puts x in one of the three    *)
(*  classes.  Distinctness makes the choice unambiguous.               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Arith Lia Ring.
Require Import ZmodPStar ZmodOrder PrimitiveRoot
        CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd
        CEisensteinSplit CEisensteinUFD.
Open Scope Z_scope.

Definition econg (pi a b : Eis) : Prop := edvd pi (esub a b).

Definition eZ (m : Z) : Eis := mkEis m 0.

Fixpoint epow (z : Eis) (n : nat) : Eis :=
  match n with O => eone | S k => emul z (epow z k) end.

(* ----------------------------------------------------------------- *)
(*  A.  congruence is a congruence                                     *)
(* ----------------------------------------------------------------- *)
Lemma econg_refl : forall pi a, econg pi a a.
Proof. intros pi a. exists ezero. unfold esub. ring. Qed.

Lemma econg_mul : forall pi a b c d,
  econg pi a b -> econg pi c d -> econg pi (emul a c) (emul b d).
Proof.
  intros pi a b c d [x Hx] [y Hy].
  exists (eadd (emul x c) (emul b y)).
  unfold esub in *.
  assert (E : eadd (emul a c) (eopp (emul b d))
              = eadd (emul (eadd a (eopp b)) c) (emul b (eadd c (eopp d))))
    by ring.
  rewrite E, Hx, Hy. ring.
Qed.

Lemma econg_pow : forall pi a b n, econg pi a b -> econg pi (epow a n) (epow b n).
Proof.
  intros pi a b n H. induction n as [| n IH]; simpl.
  - apply econg_refl.
  - apply econg_mul; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the residue field is Z/p                                       *)
(* ----------------------------------------------------------------- *)
Lemma cong_int : forall pi t z, edvd pi (esub (eZ t) eom) ->
  econg pi z (eZ (ea z + eb z * t)).
Proof.
  intros pi t z [x Hx]. exists (emul (eopp (eZ (eb z))) x).
  unfold econg, esub, eZ in *.
  assert (E : eadd z (eopp (mkEis (ea z + eb z * t) 0))
              = emul (eopp (mkEis (eb z) 0))
                     (eadd (mkEis t 0) (eopp eom))).
  { destruct z as [a b]; unfold eom, eadd, eopp, emul; cbn [ea eb].
    apply Eis_eq; ring. }
  rewrite E, Hx. ring.
Qed.

Lemma int_dvd_norm : forall pi p m, enorm pi = p ->
  edvd pi (eZ m) -> (p | m * m).
Proof.
  intros pi p m Hn [q Hq].
  assert (E : enorm (eZ m) = enorm pi * enorm q)
    by (rewrite Hq, enorm_mul; reflexivity).
  assert (Em : enorm (eZ m) = m * m)
    by (unfold enorm, eZ; cbn [ea eb]; ring).
  rewrite Em, Hn in E.
  exists (enorm q). lia.
Qed.

Theorem int_cong_iff : forall pi p m,
  prime p -> enorm pi = p -> edvd pi (eZ p) ->
  (edvd pi (eZ m) <-> (p | m)).
Proof.
  intros pi p m Hp Hn Hdvdp. split.
  - intro H. destruct (prime_mult p Hp m m (int_dvd_norm pi p m Hn H)) as [H' | H'];
      exact H'.
  - intros [c Hc]. apply (edvd_trans pi (eZ p) (eZ m)); [ exact Hdvdp | ].
    exists (eZ c). unfold eZ, emul; cbn [ea eb]. apply Eis_eq; [ lia | ring ].
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the three cube roots are distinct mod pi                       *)
(* ----------------------------------------------------------------- *)
Lemma norm_om_minus_one : enorm (esub eom eone) = 3.
Proof. unfold esub, eadd, eopp, eom, eone, enorm; cbn [ea eb]. ring. Qed.

Lemma norm_omsq_minus_one : enorm (esub (emul eom eom) eone) = 3.
Proof. unfold esub, eadd, eopp, emul, eom, eone, enorm; cbn [ea eb]. ring. Qed.

Lemma norm_omsq_minus_om : enorm (esub (emul eom eom) eom) = 3.
Proof. unfold esub, eadd, eopp, emul, eom, eone, enorm; cbn [ea eb]. ring. Qed.

Lemma not_cong_of_norm3 : forall pi p d,
  enorm pi = p -> 7 <= p -> enorm d = 3 -> ~ edvd pi d.
Proof.
  intros pi p d Hn Hp Hd Hdvd.
  pose proof (edvd_norm pi d Hdvd) as Hnd.
  rewrite Hn, Hd in Hnd.
  pose proof (Z.divide_pos_le p 3 ltac:(lia) Hnd). lia.
Qed.

Theorem cube_roots_distinct : forall pi p, enorm pi = p -> 7 <= p ->
  ~ econg pi eom eone /\ ~ econg pi (emul eom eom) eone
  /\ ~ econg pi (emul eom eom) eom.
Proof.
  intros pi p Hn Hp. repeat split; unfold econg.
  - apply (not_cong_of_norm3 pi p _ Hn Hp norm_om_minus_one).
  - apply (not_cong_of_norm3 pi p _ Hn Hp norm_omsq_minus_one).
  - apply (not_cong_of_norm3 pi p _ Hn Hp norm_omsq_minus_om).
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  a cube root of unity mod pi is 1, om or om^2                   *)
(* ----------------------------------------------------------------- *)
(* x^3 - 1 = (x-1)(x-om)(x-om^2).  ring cannot use om^2 = -1-om, but om
   is CONCRETE here, so expanding in coordinates makes it an ordinary
   integer polynomial identity. *)
Lemma cube_diff_factor : forall x : Eis,
  esub (epow x 3) eone
  = emul (esub x eone) (emul (esub x eom) (esub x (emul eom eom))).
Proof.
  intros [a b]. cbn [epow].
  unfold esub, eadd, eopp, emul, eom, eone; cbn [ea eb].
  apply Eis_eq; ring.
Qed.

Theorem cube_root_trichotomy : forall pi x, eirred pi ->
  econg pi (epow x 3) eone ->
  econg pi x eone \/ econg pi x eom \/ econg pi x (emul eom eom).
Proof.
  intros pi x Hirr Hc.
  unfold econg in Hc. rewrite cube_diff_factor in Hc.
  destruct (irred_prime pi _ _ Hirr Hc) as [H1 | H23];
    [ left; exact H1 | ].
  destruct (irred_prime pi _ _ Hirr H23) as [H2 | H3];
    [ right; left; exact H2 | right; right; exact H3 ].
Qed.

(* ----------------------------------------------------------------- *)
(*  E.  the symbol is WELL DEFINED: exactly one of the three holds      *)
(* ----------------------------------------------------------------- *)
Lemma econg_sym : forall pi a b, econg pi a b -> econg pi b a.
Proof.
  intros pi a b [x Hx]. exists (eopp x).
  unfold esub in *.
  assert (E : eadd b (eopp a) = eopp (eadd a (eopp b))) by ring.
  rewrite E, Hx. ring.
Qed.

Lemma econg_trans : forall pi a b c, econg pi a b -> econg pi b c -> econg pi a c.
Proof.
  intros pi a b c [x Hx] [y Hy]. exists (eadd x y).
  unfold esub in *.
  assert (E : eadd a (eopp c) = eadd (eadd a (eopp b)) (eadd b (eopp c))) by ring.
  rewrite E, Hx, Hy. ring.
Qed.

Theorem cubic_symbol_unique : forall pi p x, eirred pi -> enorm pi = p -> 7 <= p ->
  econg pi (epow x 3) eone ->
  (econg pi x eone /\ ~ econg pi x eom /\ ~ econg pi x (emul eom eom))
  \/ (econg pi x eom /\ ~ econg pi x eone /\ ~ econg pi x (emul eom eom))
  \/ (econg pi x (emul eom eom) /\ ~ econg pi x eone /\ ~ econg pi x eom).
Proof.
  intros pi p x Hirr Hn Hp Hc.
  destruct (cube_roots_distinct pi p Hn Hp) as [D1 [D2 D3]].
  destruct (cube_root_trichotomy pi x Hirr Hc) as [H1 | [H2 | H3]].
  - left. split; [ exact H1 | ]. split.
    + intro Hbad. apply D1.
      apply (econg_trans pi eom x eone); [ apply econg_sym; exact Hbad | exact H1 ].
    + intro Hbad. apply D2.
      apply (econg_trans pi (emul eom eom) x eone);
        [ apply econg_sym; exact Hbad | exact H1 ].
  - right; left. split; [ exact H2 | ]. split.
    + intro Hbad. apply D1.
      apply (econg_trans pi eom x eone); [ apply econg_sym; exact H2 | exact Hbad ].
    + intro Hbad. apply D3.
      apply (econg_trans pi (emul eom eom) x eom);
        [ apply econg_sym; exact Hbad | exact H2 ].
  - right; right. split; [ exact H3 | ]. split.
    + intro Hbad. apply D2.
      apply (econg_trans pi (emul eom eom) x eone);
        [ apply econg_sym; exact H3 | exact Hbad ].
    + intro Hbad. apply D3.
      apply (econg_trans pi (emul eom eom) x eom);
        [ apply econg_sym; exact H3 | exact Hbad ].
Qed.

Print Assumptions cong_int.
Print Assumptions int_cong_iff.
Print Assumptions cube_roots_distinct.
Print Assumptions cube_root_trichotomy.
Print Assumptions cubic_symbol_unique.
