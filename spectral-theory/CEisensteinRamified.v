(* ================================================================= *)
(*  CEisensteinRamified.v  --  the ramified prime lam = 1 - om.        *)
(*                                                                    *)
(*    enorm_elam    : N(1-om) = 3                                     *)
(*    elam_sq       : (1-om)^2 = -3 om                                *)
(*    three_factor  : 3 = -om^2 (1-om)^2                              *)
(*    elam_irred    : 1-om is irreducible                             *)
(*    pi_ndvd_elam  : N(pi) = p >= 7  ==>  pi does not divide 1-om    *)
(*    four_p_form   : pi primary  ==>  4 N(pi) = L^2 + 27 M^2         *)
(*                                                                    *)
(*  3 is the one rational prime that RAMIFIES in Z[om], and until now  *)
(*  the whole development has stepped around it: every lemma about     *)
(*  chiv carries the hypothesis pi | t - om for a rational t, which is *)
(*  precisely the SPLITTING condition, and the inert layer needs       *)
(*  q = 2 mod 3.  The ramified prime falls in neither camp.  Nothing   *)
(*  here is deep -- it is all ring and norm arithmetic -- but none of  *)
(*  it existed, and the second supplementary law is a statement about  *)
(*  exactly this element.                                             *)
(*                                                                    *)
(*  four_p_form is the classical shape 4p = L^2 + 27 M^2.  It comes    *)
(*  free from enorm_four (4N = (2a-b)^2 + 3b^2) once b = 3M, which is  *)
(*  the second half of primary.  That is the reason the cubic          *)
(*  character of 3 depends on b mod 9 and not on b mod 3.             *)
(*  Axiom-free.                                                       *)
(* ================================================================= *)

From Stdlib Require Import ZArith Znumtheory Lia.
Require Import CEisenstein CEisensteinUnits CEisensteinDiv CEisensteinResidue
        CEisensteinGcd CEisensteinFermat CEisensteinPrimary.
Open Scope Z_scope.

(* ----------------------------------------------------------------- *)
(*  A.  the element, its norm, and its square                          *)
(* ----------------------------------------------------------------- *)
Definition elam : Eis := esub eone eom.

Lemma elam_val : elam = mkEis 1 (-1).
Proof. reflexivity. Qed.

Theorem enorm_elam : enorm elam = 3.
Proof. reflexivity. Qed.

(* (1 - om)^2 = 1 - 2om + om^2 = 1 - 2om + (-1 - om) = -3 om *)
Theorem elam_sq : emul elam elam = eopp (emul (eZ 3) eom).
Proof. reflexivity. Qed.

(* 3 = - om^2 (1-om)^2 : the ramification identity *)
Theorem three_factor : eZ 3 = emul (eopp (emul eom eom)) (emul elam elam).
Proof. reflexivity. Qed.

(* the conjugate is 1 - om^2, and it is an associate of lam *)
Theorem econj_elam : econj elam = emul (eopp (emul eom eom)) elam.
Proof. reflexivity. Qed.

Theorem elam_conj_prod : emul elam (econj elam) = eZ 3.
Proof. reflexivity. Qed.

Lemma elam_ne0 : elam <> ezero.
Proof. discriminate. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  irreducibility, and divisibility of 3                          *)
(* ----------------------------------------------------------------- *)
Theorem elam_irred : eirred elam.
Proof.
  apply (norm_prime_eirred elam 3); [ | exact enorm_elam ].
  apply prime_3.
Qed.

Theorem elam_dvd_three : edvd elam (eZ 3).
Proof. exists (econj elam). reflexivity. Qed.

(* lam^2 divides 3 as well -- that is what "ramified" means *)
Theorem elam_sq_dvd_three : edvd (emul elam elam) (eZ 3).
Proof. exists (eopp (emul eom eom)). rewrite three_factor. ring. Qed.

(* ----------------------------------------------------------------- *)
(*  C.  a prime of norm p >= 7 misses lam                              *)
(* ----------------------------------------------------------------- *)
(*  If pi | lam then N(pi) | N(lam) = 3, so p | 3 with p >= 7.         *)
Theorem pi_ndvd_elam : forall pi p, enorm pi = p -> 7 <= p -> ~ edvd pi elam.
Proof.
  intros pi p Hn Hp7 [q Hq].
  assert (Hnn : enorm elam = enorm pi * enorm q)
    by (rewrite Hq; apply enorm_mul).
  rewrite enorm_elam, Hn in Hnn.
  pose proof (enorm_nonneg q) as Hq0.
  destruct (Z.eq_dec (enorm q) 0) as [Hz | Hz]; [ rewrite Hz in Hnn; lia | ].
  assert (H1 : 1 <= enorm q) by lia.
  assert (Hge : 7 * 1 <= p * enorm q) by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(*  D.  4p = L^2 + 27 M^2                                              *)
(* ----------------------------------------------------------------- *)
(*  Primary gives b = 3M outright; enorm_four supplies the rest.       *)
Theorem four_p_form_M : forall z, primary z ->
  4 * enorm z = (2 * ea z - eb z) * (2 * ea z - eb z)
                + 27 * ((eb z / 3) * (eb z / 3)).
Proof.
  intros z [_ Hb].
  assert (HM : eb z = 3 * (eb z / 3))
    by (pose proof (Z.div_mod (eb z) 3 ltac:(lia)) as H; lia).
  assert (Hsq : eb z * eb z = 9 * ((eb z / 3) * (eb z / 3))) by nia.
  pose proof (enorm_four z) as H4.
  lia.
Qed.

Theorem four_p_form : forall z, primary z ->
  exists L M, eb z = 3 * M /\ L = 2 * ea z - eb z
              /\ 4 * enorm z = L * L + 27 * (M * M).
Proof.
  intros z Hpr.
  exists (2 * ea z - eb z), (eb z / 3).
  destruct Hpr as [Ha Hb].
  split.
  { pose proof (Z.div_mod (eb z) 3 ltac:(lia)) as H; lia. }
  split; [ reflexivity | ].
  exact (four_p_form_M z (conj Ha Hb)).
Qed.

Print Assumptions enorm_elam.
Print Assumptions three_factor.
Print Assumptions elam_irred.
Print Assumptions pi_ndvd_elam.
Print Assumptions four_p_form.
