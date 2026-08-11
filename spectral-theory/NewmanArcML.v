(* ================================================================= *)
(*  NewmanArcML.v  —  Newman A3: integrating the arc bound (the ML step). *)
(*                                                                    *)
(*  arc_ML : the ML inequality for a circular-arc path integral,          *)
(*    |int_{arc r, a..b} f| <= 2 (M r)(b-a)   when  |f(arc r u)| <= M,     *)
(*  since |arc'(r,u)| = r (Cmod_arc') and pathint = Cintf(f o arc . arc'). *)
(*                                                                    *)
(*  newman_arc_ML : the O(B/R) right-semicircle bound -- feeding the        *)
(*  pointwise 4B/R^2 bound (right_arc_bound) over the arc [-pi/2, pi/2]     *)
(*  gives  |int_arc (g-g_T) e^{zT} K_R| <= 8 pi B / R  ->  0 as R -> oo.    *)
(*  Axiom-clean.                                                         *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CIntegral2 CSegInt CPathIntegral.
Open Scope R_scope.

Lemma arc_ML : forall (f : C -> C) (r a b M : R)
  (Hf : Ccont (fun u => Cmul (f (arc r u)) (arc' r u))),
  0 <= r -> a <= b ->
  (forall u, a <= u <= b -> Cmod (f (arc r u)) <= M) ->
  Cmod (pathint (arc r) (arc' r) f Hf a b) <= 2 * (M * r) * (b - a).
Proof.
  intros f r a b M Hf Hr Hab Hbd; unfold pathint.
  apply (Cintf_ML (fun u => Cmul (f (arc r u)) (arc' r u)) Hf a b (M * r) Hab).
  intros u Hu; rewrite Cmod_mul, (Cmod_arc' r u Hr).
  apply Rmult_le_compat_r; [ exact Hr | apply Hbd; exact Hu ].
Qed.

Corollary newman_arc_ML : forall (f : C -> C) (R B : R)
  (Hf : Ccont (fun u => Cmul (f (arc R u)) (arc' R u))),
  0 < R ->
  (forall u, - (PI / 2) <= u <= PI / 2 -> Cmod (f (arc R u)) <= 4 * B / (R * R)) ->
  Cmod (pathint (arc R) (arc' R) f Hf (- (PI / 2)) (PI / 2)) <= 8 * PI * B / R.
Proof.
  intros f R B Hf HR Hbd; pose proof PI_RGT_0 as HPI.
  eapply Rle_trans;
    [ apply (arc_ML f R (- (PI / 2)) (PI / 2) (4 * B / (R * R)) Hf);
        [ lra | lra | exact Hbd ]
    | apply Req_le; field; apply Rgt_not_eq; exact HR ].
Qed.

Print Assumptions arc_ML.
Print Assumptions newman_arc_ML.

(* ================================================================= *)
(*  END NewmanArcML.v — the O(B/R) right-semicircle arc bound.            *)
(*  With right_arc_bound (the pointwise 4B/R^2 on the open arc) this is     *)
(*  the O(B/R) right piece of Newman's contour estimate.  Remaining: the    *)
(*  left-half-plane pieces (g by analytic continuation e^{zT}->0, g_T        *)
(*  entire), Cauchy's formula on the contour, and the T->oo, R->oo limits.  *)
(* ================================================================= *)
