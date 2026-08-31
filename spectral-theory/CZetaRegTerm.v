(* CZetaRegTerm.v -- the pole-free rewriting of the Euler-Maclaurin term.

   CZetaTerm.gtermC s n = a^{-s} - [ b^{1-s} - a^{1-s} ] / (1-s),
   with a = n+1, b = n+2.  The bracket is a difference quotient in
   disguise: with w = 1-s and L = ln(b/a),

       [ b^w - a^w ] / w  =  a^w * (e^{wL} - 1) / w  =  a^w * L * E(wL),

   and E is entire (CExpEntire.Eexp_entire).  So rterm below agrees with
   gtermC wherever gtermC is defined, and unlike gtermC it is defined --
   and holomorphic -- at s = 1 as well.

   Sanity: at s = 1 (w = 0) we get rterm = 1/(n+1) - ln((n+2)/(n+1)),
   whose sum over n is Euler-Mascheroni gamma.  That is exactly
   lim_{s->1} (zeta(s) - 1/(s-1)), so the regularisation lands on the
   correct value at the pole. *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus EulerFormula CexpFull CexpfDeriv
        CexpRemainder CExpQuot CExpEntire Holomorphic CDeriv CHoloCalculus
        CCutoff CPowBase CSeries CZetaTerm.
Open Scope R_scope.

Lemma RtoC_minus' : forall r s, RtoC (r - s) = Cminus (RtoC r) (RtoC s).
Proof. intros r s; apply Ceq; simpl; ring. Qed.

Lemma ln_quot : forall a b, 0 < a -> 0 < b -> ln (b / a) = ln b - ln a.
Proof.
  intros a b Ha Hb. unfold Rdiv.
  rewrite ln_mult; [ | exact Hb | apply Rinv_0_lt_compat; exact Ha ].
  rewrite ln_Rinv; [ ring | exact Ha ].
Qed.

(* ---- the regularised term ---- *)

Definition rterm (s : C) (n : nat) : C :=
  Cminus (gC s (INR (S n)))
    (Cmul (Cpw (INR (S n)) (Cminus C1 s))
      (Cmul (RtoC (ln (INR (S (S n)) / INR (S n))))
            (Eexp (Cmul (Cminus C1 s)
                     (RtoC (ln (INR (S (S n)) / INR (S n)))))))).

Theorem rterm_eq : forall s n,
  Cminus C1 s <> C0 -> rterm s n = gtermC s n.
Proof.
  intros s n Hw.
  assert (Ha : 0 < INR (S n)) by (apply lt_0_INR; lia).
  assert (Hb : 0 < INR (S (S n))) by (apply lt_0_INR; lia).
  unfold rterm, gtermC, GC.
  set (a := INR (S n)) in *. set (b := INR (S (S n))) in *.
  set (w := Cminus C1 s) in *.
  set (L := RtoC (ln (b / a))) in *.
  (* Step A: b^w = a^w * e^{wL} *)
  assert (HA : Cpw b w = Cmul (Cpw a w) (Cexpf (Cmul w L))).
  { unfold Cpw. rewrite <- Cexpf_add. f_equal.
    unfold L. rewrite (ln_quot a b Ha Hb).
    rewrite RtoC_minus'. ring. }
  (* Step B: E(wL) * (wL) = e^{wL} - 1 *)
  assert (HB : Cmul (Eexp (Cmul w L)) (Cmul w L)
               = Cminus (Cexpf (Cmul w L)) C1) by apply Eexp_spec.
  (* Step C: w cancels *)
  assert (Hwi : Cmul w (Cinv w) = C1).
  { replace (Cmul w (Cinv w)) with (Cmul (Cinv w) w) by ring.
    apply Cinv_l; exact Hw. }
  assert (KEY : Cminus (Cmul (Cpw b w) (Cinv w)) (Cmul (Cpw a w) (Cinv w))
                = Cmul (Cpw a w) (Cmul L (Eexp (Cmul w L)))).
  { rewrite HA.
    replace (Cminus (Cmul (Cmul (Cpw a w) (Cexpf (Cmul w L))) (Cinv w))
                    (Cmul (Cpw a w) (Cinv w)))
      with (Cmul (Cpw a w) (Cmul (Cminus (Cexpf (Cmul w L)) C1) (Cinv w)))
      by ring.
    rewrite <- HB.
    replace (Cmul (Cpw a w) (Cmul (Cmul (Eexp (Cmul w L)) (Cmul w L)) (Cinv w)))
      with (Cmul (Cmul (Cpw a w) (Cmul L (Eexp (Cmul w L)))) (Cmul w (Cinv w)))
      by ring.
    rewrite Hwi. ring. }
  rewrite KEY. reflexivity.
Qed.

(* ---- the value at the pole: rterm is the Euler-Mascheroni summand ----

   gtermC is undefined (in the encoding, wrongly defined) at s = 1.
   rterm is defined there, and equals 1/(n+1) - ln((n+2)/(n+1)) --
   whose sum over n is gamma = lim_{s->1} (zeta(s) - 1/(s-1)).
   This is an independent check that the regularisation is the right
   one: nothing in rterm_eq forces this value, it falls out. *)

Theorem rterm_at_one : forall n,
  rterm C1 n
  = RtoC (/ INR (S n) - ln (INR (S (S n)) / INR (S n))).
Proof.
  intro n.
  assert (Ha : 0 < INR (S n)) by (apply lt_0_INR; lia).
  unfold rterm, gC.
  replace (Cminus C1 C1) with C0 by ring.
  (* a^0 = 1 *)
  assert (HP : Cpw (INR (S n)) C0 = C1).
  { unfold Cpw. replace (Cmul C0 (RtoC (ln (INR (S n))))) with C0 by ring.
    apply Cexpf_at0. }
  rewrite HP.
  (* E(0) = 1 *)
  replace (Cmul C0 (RtoC (ln (INR (S (S n)) / INR (S n))))) with C0 by ring.
  rewrite Eexp_at0.
  (* a^{-1} = 1/a *)
  assert (HG : Cpw (INR (S n)) (Copp C1) = RtoC (/ INR (S n))).
  { unfold Cpw.
    replace (Cmul (Copp C1) (RtoC (ln (INR (S n)))))
      with (RtoC (- ln (INR (S n)))) by (apply Ceq; simpl; ring).
    rewrite Cexpf_RtoC. rewrite exp_Ropp, exp_ln by exact Ha. reflexivity. }
  rewrite HG.
  rewrite RtoC_minus'. apply Ceq; simpl; ring.
Qed.
