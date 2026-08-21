(* ================================================================= *)
(*  CEisensteinInert.v  —  p = 2 mod 3 stays PRIME in Z[omega].        *)
(*                                                                    *)
(*    sq_mod3          : squares are 0 or 1 mod 3                      *)
(*    enorm_mod3       : N(z) is 0 or 1 mod 3, never 2                 *)
(*    no_norm_2mod3    : nothing has norm = 2 mod 3                    *)
(*    eisenstein_inert : p = 2 mod 3 prime => p is irreducible         *)
(*                                                                    *)
(*  Together with CEisensteinSplit this classifies the rational        *)
(*  primes in Z[omega]: p = 1 mod 3 splits as pi . conj pi, and        *)
(*  p = 2 mod 3 stays inert.  (p = 3 ramifies, 3 = -omega^2 (1-omega)^2,*)
(*  and is not treated here.)                                          *)
(*                                                                    *)
(*  THE OBSTRUCTION IS A CONGRUENCE, and 4N = (2a-b)^2 + 3b^2 -- the   *)
(*  same identity that gave nonnegativity of the norm and the six      *)
(*  units -- delivers it a third time.  Mod 3 the 3b^2 term vanishes   *)
(*  and 4 = 1, so N = (2a-b)^2 (mod 3); squares mod 3 are 0 or 1, so   *)
(*  N is never 2 mod 3.  No case analysis on a and b separately is     *)
(*  needed, only on one residue.                                       *)
(*                                                                    *)
(*  no_norm_2mod3 needs no primality at all -- it is pure congruence.  *)
(*  Primality enters only to force N(d) = p in a factorisation, which  *)
(*  is then what the congruence forbids.  Axiom-clean.                 *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia Ring.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinGcd.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  squares mod 3                                                  *)
(* ----------------------------------------------------------------- *)
Lemma sq_mod3 : forall s : Z, (s * s) mod 3 = 0 \/ (s * s) mod 3 = 1.
Proof.
  intro s.
  assert (Hr : 0 <= s mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (H3 : s mod 3 = 0 \/ s mod 3 = 1 \/ s mod 3 = 2) by lia.
  rewrite (Z.mul_mod s s 3) by lia.
  destruct H3 as [H | [H | H]]; rewrite H.
  - left; reflexivity.
  - right; reflexivity.
  - right; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the norm is never 2 mod 3                                      *)
(* ----------------------------------------------------------------- *)
Lemma enorm_mod3 : forall z, enorm z mod 3 = 0 \/ enorm z mod 3 = 1.
Proof.
  intro z.
  pose proof (enorm_four z) as H4.
  set (s := 2 * ea z - eb z).
  (* N - s^2 = 3 (b^2 - N), so N and s^2 agree mod 3 *)
  assert (Hdvd : (3 | enorm z - s * s)).
  { exists (eb z * eb z - enorm z). unfold s in *. nia. }
  assert (Hz0 : (enorm z - s * s) mod 3 = 0)
    by (apply Z.mod_divide; [ lia | exact Hdvd ]).
  rewrite Zminus_mod in Hz0.
  assert (Hr1 : 0 <= enorm z mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (Hr2 : 0 <= (s * s) mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (Hcong : enorm z mod 3 = (s * s) mod 3).
  { apply Z.mod_divide in Hz0; [ | lia ].
    destruct Hz0 as [c Hc]. lia. }
  rewrite Hcong. apply sq_mod3.
Qed.

Theorem no_norm_2mod3 : forall (m : Z), m mod 3 = 2 -> forall z, enorm z <> m.
Proof.
  intros m Hm z Hc.
  destruct (enorm_mod3 z) as [H | H]; rewrite Hc, Hm in H; lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  such a prime is irreducible                                    *)
(* ----------------------------------------------------------------- *)
Theorem eisenstein_inert : forall p : nat,
  prime (Z.of_nat p) -> (p mod 3 = 2)%nat -> eirred (mkEis (Z.of_nat p) 0).
Proof.
  intros p Hp Hm.
  set (P := Z.of_nat p).
  assert (HP2 : 2 <= P) by (destruct Hp; unfold P; lia).
  assert (HPm : P mod 3 = 2).
  { unfold P. replace 3 with (Z.of_nat 3) by reflexivity.
    rewrite <- Nat2Z.inj_mod, Hm. reflexivity. }
  set (Pe := mkEis P 0).
  assert (HPe : enorm Pe = P * P) by (unfold Pe, enorm; cbn [ea eb]; ring).
  repeat split.
  - (* not a unit *)
    intro Hu. apply eunit_norm in Hu. rewrite HPe in Hu. nia.
  - (* nonzero *)
    intro Hc. unfold Pe in Hc.
    assert (P = 0) by (inversion Hc; reflexivity). lia.
  - (* irreducible *)
    intros d q Hdq.
    destruct (Z.eq_dec (enorm d) 1) as [Hgu | Hgnu];
      [ left; apply norm_eunit; exact Hgu | ].
    destruct (Z.eq_dec (enorm q) 1) as [Hhu | Hhnu];
      [ right; apply norm_eunit; exact Hhu | ].
    exfalso.
    assert (Hnorms : enorm d * enorm q = P * P)
      by (rewrite <- HPe, Hdq, enorm_mul; reflexivity).
    assert (Hd0 : 0 <= enorm d) by apply enorm_nonneg.
    assert (Hq0 : 0 <= enorm q) by apply enorm_nonneg.
    assert (HdvdP : (P | enorm d * enorm q)) by (exists P; lia).
    (* one of the two norms is exactly P, which the congruence forbids *)
    destruct (prime_mult P Hp _ _ HdvdP) as [[m Hmd] | [m Hmq]].
    + assert (Hmdvd : (m | P)) by (exists (enorm q); nia).
      assert (HdP : enorm d = P \/ enorm d = P * P).
      { destruct (prime_divisors P Hp m Hmdvd) as [E | [E | [E | E]]].
        - exfalso; nia.
        - left; nia.
        - right; nia.
        - exfalso; nia. }
      destruct HdP as [HdP | HdP].
      * exact (no_norm_2mod3 P HPm d HdP).
      * apply Hhnu. nia.
    + assert (Hmdvd : (m | P)) by (exists (enorm d); nia).
      assert (HqP : enorm q = P \/ enorm q = P * P).
      { destruct (prime_divisors P Hp m Hmdvd) as [E | [E | [E | E]]].
        - exfalso; nia.
        - left; nia.
        - right; nia.
        - exfalso; nia. }
      destruct HqP as [HqP | HqP].
      * exact (no_norm_2mod3 P HPm q HqP).
      * apply Hgnu. nia.
Qed.

Print Assumptions enorm_mod3.
Print Assumptions eisenstein_inert.
