(* ================================================================= *)
(*  CEisenstein.v  —  the ring Z[omega] and its NORM.                  *)
(*                                                                    *)
(*    Eis        : a + b.om  with a, b in Z                            *)
(*    emul       : (a+b om)(c+d om) = (ac-bd) + (ad+bc-bd) om          *)
(*    enorm z    := a^2 - ab + b^2                                     *)
(*    enorm_mul  : N(zw) = N(z) N(w)                                   *)
(*    enorm_nonneg, enorm_zero : N(z) >= 0, and N(z) = 0 iff z = 0     *)
(*    eimg       : the embedding into C, a ring homomorphism           *)
(*    enorm_eq_Cnorm2 : N(z) = |eimg z|^2                              *)
(*                                                                    *)
(*  The multiplication rule is where om^2 = -1 - om does its work:     *)
(*  the bd om^2 term folds back down, which is why the coefficient of  *)
(*  om is ad + bc - bd rather than the naive ad + bc.  Everything      *)
(*  after that is polynomial identity over Z -- enorm_mul is a single  *)
(*  ring call once emul is right, and getting emul wrong would make it *)
(*  simply false.                                                     *)
(*                                                                    *)
(*  enorm_eq_Cnorm2 is the lemma that earns the name: it shows the     *)
(*  ALGEBRAIC norm a^2-ab+b^2 is the ANALYTIC |.|^2 under the          *)
(*  embedding, and its proof is COmega.eisenstein_norm_om together     *)
(*  with conj om = om^2.  That is the same norm form                   *)
(*  crypto/PrimeFactorizationTriadic.eisenstein_norm (:135) defined    *)
(*  and never connected to anything.                                   *)
(*                                                                    *)
(*  N(z) >= 0 is not automatic from the shape: a^2 - ab + b^2 has a    *)
(*  negative middle term.  It is 4N = (2a-b)^2 + 3b^2 that makes it    *)
(*  obvious, and that is how it is proved.  Axiom-clean.               *)
(* ================================================================= *)

From Stdlib Require Import ZArith Lia Reals Lra.
Require Import ComplexField Cmodulus RootsOfUnity COmega.
Open Scope Z_scope.

Record Eis : Set := mkEis { ea : Z; eb : Z }.

Definition ezero : Eis := mkEis 0 0.
Definition eone  : Eis := mkEis 1 0.
Definition eom   : Eis := mkEis 0 1.

Definition eadd (z w : Eis) : Eis := mkEis (ea z + ea w) (eb z + eb w).
Definition eopp (z : Eis) : Eis := mkEis (- ea z) (- eb z).

(* (a + b om)(c + d om) = ac + (ad+bc) om + bd om^2,  and om^2 = -1 - om *)
Definition emul (z w : Eis) : Eis :=
  mkEis (ea z * ea w - eb z * eb w)
        (ea z * eb w + eb z * ea w - eb z * eb w).

Definition enorm (z : Eis) : Z := ea z * ea z - ea z * eb z + eb z * eb z.

Lemma Eis_eq : forall a b c d, a = c -> b = d -> mkEis a b = mkEis c d.
Proof. intros a b c d Hac Hbd; subst; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(*  A.  ring laws                                                      *)
(* ----------------------------------------------------------------- *)
Lemma eadd_comm : forall z w, eadd z w = eadd w z.
Proof. intros [a b] [c d]; unfold eadd; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma eadd_assoc : forall x y z, eadd (eadd x y) z = eadd x (eadd y z).
Proof. intros [a b] [c d] [e f]; unfold eadd; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma eadd_0 : forall z, eadd ezero z = z.
Proof. intros [a b]; unfold eadd, ezero; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma eadd_opp : forall z, eadd z (eopp z) = ezero.
Proof. intros [a b]; unfold eadd, eopp, ezero; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma emul_comm : forall z w, emul z w = emul w z.
Proof. intros [a b] [c d]; unfold emul; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma emul_assoc : forall x y z, emul (emul x y) z = emul x (emul y z).
Proof. intros [a b] [c d] [e f]; unfold emul; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma emul_1 : forall z, emul eone z = z.
Proof. intros [a b]; unfold emul, eone; cbn [ea eb]; apply Eis_eq; ring. Qed.

Lemma emul_distr : forall x y z, emul x (eadd y z) = eadd (emul x y) (emul x z).
Proof. intros [a b] [c d] [e f]; unfold emul, eadd; cbn [ea eb]; apply Eis_eq; ring. Qed.

(* om really is a cube root of unity in the ring *)
Theorem eom_cube : emul eom (emul eom eom) = eone.
Proof. unfold emul, eom, eone; cbn [ea eb]; apply Eis_eq; ring. Qed.

Theorem eom_one_plus : eadd eone (eadd eom (emul eom eom)) = ezero.
Proof. unfold eadd, emul, eom, eone, ezero; cbn [ea eb]; apply Eis_eq; ring. Qed.

(* ----------------------------------------------------------------- *)
(*  B.  the norm                                                       *)
(* ----------------------------------------------------------------- *)
Theorem enorm_mul : forall z w, enorm (emul z w) = enorm z * enorm w.
Proof. intros [a b] [c d]; unfold enorm, emul; cbn [ea eb]; ring. Qed.

(* 4 N(z) = (2a - b)^2 + 3 b^2 : the reason the norm is nonnegative *)
Lemma enorm_four : forall z,
  4 * enorm z = (2 * ea z - eb z) * (2 * ea z - eb z) + 3 * (eb z * eb z).
Proof. intros [a b]; unfold enorm; cbn [ea eb]; ring. Qed.

Theorem enorm_nonneg : forall z, 0 <= enorm z.
Proof.
  intro z. pose proof (enorm_four z) as H. nia.
Qed.

Theorem enorm_zero : forall z, enorm z = 0 <-> z = ezero.
Proof.
  intro z. split.
  - intro H. pose proof (enorm_four z) as H4.
    destruct z as [a b]; cbn [ea eb] in *; unfold ezero.
    assert (Ha : a = 0) by nia. assert (Hb : b = 0) by nia.
    rewrite Ha, Hb. reflexivity.
  - intro H. rewrite H. unfold enorm, ezero; cbn [ea eb]; ring.
Qed.

(* ----------------------------------------------------------------- *)
(*  C.  the embedding into C, and the norm as a modulus                *)
(* ----------------------------------------------------------------- *)
Lemma RtoC_Zadd : forall x y : Z,
  RtoC (IZR (x + y)) = Cadd (RtoC (IZR x)) (RtoC (IZR y)).
Proof.
  intros x y. rewrite plus_IZR. unfold RtoC, Cadd.
  apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma RtoC_Zsub : forall x y : Z,
  RtoC (IZR (x - y)) = Cminus (RtoC (IZR x)) (RtoC (IZR y)).
Proof.
  intros x y. rewrite minus_IZR. unfold RtoC, Cminus, Cadd, Copp.
  apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma RtoC_Zmul : forall x y : Z,
  RtoC (IZR (x * y)) = Cmul (RtoC (IZR x)) (RtoC (IZR y)).
Proof.
  intros x y. rewrite mult_IZR. unfold RtoC, Cmul.
  apply Ceq; cbn [Re Im]; ring.
Qed.

Lemma Cconj_RtoC : forall r, Cconj (RtoC r) = RtoC r.
Proof. intro r. unfold RtoC, Cconj. apply Ceq; cbn [Re Im]; ring. Qed.

Lemma RtoC_inj : forall x y, RtoC x = RtoC y -> x = y.
Proof.
  intros x y H. apply (f_equal Re) in H. unfold RtoC in H; cbn [Re] in H.
  exact H.
Qed.

Definition eimg (z : Eis) : C :=
  Cadd (RtoC (IZR (ea z))) (Cmul (RtoC (IZR (eb z))) om).

Lemma eimg_add : forall z w, eimg (eadd z w) = Cadd (eimg z) (eimg w).
Proof.
  intros [a b] [c d]. unfold eimg, eadd; cbn [ea eb].
  rewrite !RtoC_Zadd. ring.
Qed.

Lemma eimg_mul : forall z w, eimg (emul z w) = Cmul (eimg z) (eimg w).
Proof.
  intros [a b] [c d]. unfold eimg, emul; cbn [ea eb].
  rewrite !RtoC_Zsub, !RtoC_Zadd, !RtoC_Zmul.
  set (A := RtoC (IZR a)). set (B := RtoC (IZR b)).
  set (D := RtoC (IZR c)). set (E := RtoC (IZR d)).
  assert (F : Cmul (Cadd A (Cmul B om)) (Cadd D (Cmul E om))
              = Cadd (Cmul A D)
                (Cadd (Cmul (Cadd (Cmul A E) (Cmul B D)) om)
                      (Cmul (Cmul B E) (Cmul om om)))) by ring.
  rewrite F, om_sq. ring.
Qed.

(* conj om = om^2 : both are the inverse of om, since om.conj om = |om|^2
   = 1 = om.om^2.  No cancellation needed -- just multiply through. *)
Lemma Cnorm2_om : Cnorm2 om = 1%R.
Proof.
  unfold om, w, Cnorm2; cbn [Re Im].
  pose proof (sin2_cos2 (2 * PI / INR 3)%R); unfold Rsqr in *; nra.
Qed.

Lemma Cconj_om : Cconj om = Cmul om om.
Proof.
  assert (H1 : Cmul om (Cconj om) = C1)
    by (rewrite Cmul_conj, Cnorm2_om; reflexivity).
  assert (H2 : Cmul om (Cmul om om) = C1) by apply om_cube.
  assert (E : Cmul (Cconj om) (Cmul om (Cmul om om))
              = Cmul (Cmul om (Cconj om)) (Cmul om om)) by ring.
  rewrite H1, H2 in E.
  transitivity (Cmul (Cconj om) C1); [ ring | rewrite E; ring ].
Qed.

Theorem enorm_eq_Cnorm2 : forall z, IZR (enorm z) = Cnorm2 (eimg z).
Proof.
  intros [a b]. symmetry. apply RtoC_inj.
  rewrite <- Cmul_conj.
  unfold eimg; cbn [ea eb].
  rewrite Cconj_add, Cconj_mul, Cconj_om, !Cconj_RtoC.
  replace (Cmul (Cadd (RtoC (IZR a)) (Cmul (RtoC (IZR b)) om))
                (Cadd (RtoC (IZR a)) (Cmul (RtoC (IZR b)) (Cmul om om))))
    with (Cmul (Cadd (RtoC (IZR a)) (Cmul om (RtoC (IZR b))))
               (Cadd (RtoC (IZR a)) (Cmul (Cmul om om) (RtoC (IZR b)))))
    by ring.
  rewrite (eisenstein_norm_om (RtoC (IZR a)) (RtoC (IZR b))).
  unfold enorm; cbn [ea eb].
  rewrite RtoC_Zadd, RtoC_Zsub, !RtoC_Zmul. reflexivity.
Qed.

Print Assumptions enorm_mul.
Print Assumptions eimg_mul.
Print Assumptions enorm_eq_Cnorm2.
