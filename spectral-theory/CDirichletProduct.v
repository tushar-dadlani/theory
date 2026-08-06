(* ================================================================= *)
(*  CDirichletProduct.v  —  Milestone A / B3e: the Dirichlet product.   *)
(*                                                                    *)
(*  Assembles B3a-B3d into the complex Dirichlet-series product law:    *)
(*  if the term-series Sum A_d -> SA and Sum B_m -> SB converge, and     *)
(*  both converge absolutely (Sum |A_d|, Sum |B_m| converge), then the   *)
(*  Dirichlet-convolution series                                        *)
(*     Sum_{n>=1} ( Sum_{d|n} A_d B_{n/d} )  ->  SA * SB.                *)
(*  Proof: the hyperbolic partial sum H_N (= the convolution partial     *)
(*  sum, by Chyperbola_swap) differs from the square P_N = (Sum A)(Sum B)*)
(*  by the corner Csq_hyp_bound, whose modulus -> 0 by corner_cv0.  Since *)
(*  P_N -> SA*SB (CUn_cv_mul), so does H_N.                              *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia Arith List.
Require Import ComplexField Cmodulus CListSum RealMobius MobiusOverD
        CDirichlet CSeries GammaFunction CDirichletExhaustion CDirichletTail
        VonMangoldtGlobal CHyperbolaSwap.
Import ListNotations.
Open Scope R_scope.

(* ---- complex product of convergent sequences (componentwise) ---- *)
Lemma CUn_cv_mul : forall u v a c, CUn_cv u a -> CUn_cv v c ->
  CUn_cv (fun n => Cmul (u n) (v n)) (Cmul a c).
Proof.
  intros u v a c Hu Hv.
  apply CUn_cv_comp; rewrite CUn_cv_comp in Hu, Hv.
  destruct Hu as [HuR HuI]; destruct Hv as [HvR HvI]; split.
  - apply (Un_cv_ext (fun n => Re (u n) * Re (v n) - Im (u n) * Im (v n)));
      [ intro n; unfold Cmul; cbn [Re]; ring | ].
    replace (Re (Cmul a c)) with (Re a * Re c - Im a * Im c)
      by (unfold Cmul; cbn [Re]; ring).
    apply CV_minus; apply CV_mult; assumption.
  - apply (Un_cv_ext (fun n => Re (u n) * Im (v n) + Im (u n) * Re (v n)));
      [ intro n; unfold Cmul; cbn [Im]; ring | ].
    replace (Im (Cmul a c)) with (Re a * Im c + Im a * Re c)
      by (unfold Cmul; cbn [Im]; ring).
    apply CV_plus; apply CV_mult; assumption.
Qed.

(* ---- local: componentwise limit of a complex difference ---- *)
Lemma CUn_cv_minus : forall u v a c, CUn_cv u a -> CUn_cv v c ->
  CUn_cv (fun n => Cminus (u n) (v n)) (Cminus a c).
Proof.
  intros u v a c Hu Hv.
  apply CUn_cv_comp; rewrite CUn_cv_comp in Hu, Hv.
  destruct Hu as [HuR HuI]; destruct Hv as [HvR HvI]; split.
  - apply (Un_cv_ext (fun n => Re (u n) - Re (v n)));
      [ intro n; unfold Cminus, Cadd, Copp; cbn [Re]; ring | ].
    replace (Re (Cminus a c)) with (Re a - Re c)
      by (unfold Cminus, Cadd, Copp; cbn [Re]; ring).
    apply CV_minus; assumption.
  - apply (Un_cv_ext (fun n => Im (u n) - Im (v n)));
      [ intro n; unfold Cminus, Cadd, Copp; cbn [Im]; ring | ].
    replace (Im (Cminus a c)) with (Im a - Im c)
      by (unfold Cminus, Cadd, Copp; cbn [Im]; ring).
    apply CV_minus; assumption.
Qed.

(* ---- THE complex Dirichlet-series product ---- *)
Theorem cdirichlet_product : forall (A B : nat -> C) SA SB TA TB,
  CUn_cv (fun N => Cls (seq 1 N) A) SA ->
  CUn_cv (fun N => Cls (seq 1 N) B) SB ->
  Un_cv (fun N => Rls (seq 1 N) (fun d => Cmod (A d))) TA ->
  Un_cv (fun N => Rls (seq 1 N) (fun m => Cmod (B m))) TB ->
  CUn_cv (fun N => Cls (seq 1 N)
    (fun n => Cls (divisors n) (fun d => Cmul (A d) (B (n / d)%nat)))) (Cmul SA SB).
Proof.
  intros A B SA SB TA TB HAcv HBcv HTA HTB.
  (* the corner modulus -> 0 *)
  assert (Hd0 : Un_cv (fun N => Cmod (Cminus
      (Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)) (Chyp N A B))) 0).
  { apply (Un_cv_squeeze0 _ (fun N => Rls (seq 1 N)
        (fun d => Cmod (A d) * Rls (seq (S (N / d)) (N - N / d)) (fun m => Cmod (B m))))).
    - exists 0%nat; intros N _; split; [ apply Cmod_nonneg | apply Csq_hyp_bound ].
    - apply (corner_cv0 (fun d => Cmod (A d)) (fun m => Cmod (B m))
               (fun d => Cmod_nonneg (A d)) (fun m => Cmod_nonneg (B m)) TA TB HTA HTB). }
  (* P_N -> SA*SB *)
  assert (Hprod : CUn_cv (fun N => Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)) (Cmul SA SB))
    by (apply CUn_cv_mul; assumption).
  (* P_N - H_N -> 0 *)
  assert (Hdiff : CUn_cv (fun N => Cminus
      (Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)) (Chyp N A B)) C0)
    by (apply CUn_cv_mod0; exact Hd0).
  (* hence H_N -> SA*SB *)
  assert (Hchyp : CUn_cv (fun N => Chyp N A B) (Cmul SA SB)).
  { apply (CUn_cv_ext (fun N => Cminus (Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B))
             (Cminus (Cmul (Cls (seq 1 N) A) (Cls (seq 1 N) B)) (Chyp N A B)))).
    - intro N; ring.
    - replace (Cmul SA SB) with (Cminus (Cmul SA SB) C0) by ring.
      apply CUn_cv_minus; [ exact Hprod | exact Hdiff ]. }
  (* rewrite the divisor form to H_N via Chyperbola_swap *)
  apply (CUn_cv_ext (fun N => Chyp N A B)); [ | exact Hchyp ].
  intro N; unfold Chyp; symmetry.
  apply (Chyperbola_swap (fun d m => Cmul (A d) (B m)) N).
Qed.

Print Assumptions cdirichlet_product.

(* ================================================================= *)
(*  END CDirichletProduct.v  —  Sum_{d|n} A_d B_{n/d} -> SA*SB.         *)
(* ================================================================= *)
