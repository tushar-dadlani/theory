(* ================================================================= *)
(*  CPrimitive.v  —  Milestone C, brick C2b: a holomorphic function has  *)
(*  a primitive, hence its loop integrals vanish (from Goursat).        *)
(*                                                                    *)
(*  For F holomorphic everywhere, Prim z := ∫ from a basepoint z0 to z    *)
(*  along the segment is a primitive: Prim'(z) = F(z).  The key step is   *)
(*  Prim(z+k) − Prim(z) = ∫_z^{z+k} F (Goursat kills the triangle         *)
(*  z0,z,z+k), and ∫_z^{z+k}(F(w)−F(z))dw is o(k) by continuity + ML.     *)
(*  Then pathint over any closed path = 0 (path FTC).                    *)
(* ================================================================= *)

From Stdlib Require Import Reals Lra Lia.
Require Import ComplexField Cmodulus CSeries CImproperIntegral Holomorphic
        CHoloCalculus CIntegral2 CPathIntegral CPathFTC CSegInt CTriangle
        CGoursatLin CGoursatML CGoursat.
Open Scope R_scope.

(* ---- constant / opp / sub segment integrals ---- *)
Lemma CcontC_const : forall c, CcontC (fun _ => c).
Proof. intros c gam Hgam; apply Ccont_const. Qed.

Lemma Cintf_const01 : forall k Hk, Cintf (fun _ => k) Hk 0 1 = k.
Proof.
  intros k Hk; apply Ceq; cbn [Re Im].
  - transitivity (Re k * (1 - 0));
      [ exact (RiemannInt_P15 (cont_RI _ (proj1 Hk) 0 1)) | ring ].
  - transitivity (Im k * (1 - 0));
      [ exact (RiemannInt_P15 (cont_RI _ (proj2 Hk) 0 1)) | ring ].
Qed.

Lemma seg_int_const : forall c (Hc : CcontC (fun _ => c)) a b,
  seg_int (fun _ => c) Hc a b = Cmul c (Cminus b a).
Proof.
  intros c Hc a b; unfold seg_int.
  transitivity (Cintf (fun _ => Cmul c (Cminus b a))
                 (Ccont_const (Cmul c (Cminus b a))) 0 1).
  - apply Cintf_ext; intro u; unfold seg'; reflexivity.
  - apply Cintf_const01.
Qed.

Lemma seg_int_opp : forall g (Hg : CcontC g) (Hog : CcontC (fun w => Copp (g w))) a b,
  seg_int (fun w => Copp (g w)) Hog a b = Copp (seg_int g Hg a b).
Proof.
  intros g Hg Hog a b.
  assert (Hz : seg_int (fun w => Cadd (g w) (Copp (g w)))
                 (CcontC_add g (fun w => Copp (g w)) Hg Hog) a b = C0).
  { transitivity (seg_int (fun _ => C0) (CcontC_const C0) a b).
    - apply seg_int_ext; intro z; ring.
    - rewrite seg_int_const; ring. }
  rewrite (seg_int_add g (fun w => Copp (g w)) Hg Hog
            (CcontC_add g (fun w => Copp (g w)) Hg Hog) a b) in Hz.
  (* Cadd (seg_int g)(seg_int (Copp g)) = C0 ⇒ seg_int (Copp g) = Copp (seg_int g) *)
  assert (HR := f_equal Re Hz); assert (HI := f_equal Im Hz).
  apply Ceq; unfold Cadd, Copp, C0 in *; cbn in *; lra.
Qed.

Lemma seg_int_sub : forall f g (Hf : CcontC f) (Hg : CcontC g)
  (Hfg : CcontC (fun w => Cminus (f w) (g w))) a b,
  seg_int (fun w => Cminus (f w) (g w)) Hfg a b
  = Cminus (seg_int f Hf a b) (seg_int g Hg a b).
Proof.
  intros f g Hf Hg Hfg a b.
  assert (Hog : CcontC (fun w => Copp (g w))) by (apply CcontC_opp; exact Hg).
  transitivity (seg_int (fun w => Cadd (f w) (Copp (g w)))
                 (CcontC_add f (fun w => Copp (g w)) Hf Hog) a b).
  - apply seg_int_ext; intro z; ring.
  - rewrite (seg_int_add f (fun w => Copp (g w)) Hf Hog
              (CcontC_add f (fun w => Copp (g w)) Hf Hog) a b).
    rewrite (seg_int_opp g Hg Hog a b); ring.
Qed.

Section Primitive.
Variable F : C -> C.
Variable HF : CcontC F.
Hypothesis Hhol : forall z, exists d, is_Cderiv F z d.
Variable z0 : C.

Definition Prim (z : C) : C := seg_int F HF z0 z.

(* F is continuous at each point (Cmod sense) *)
Lemma Fcont_pt : forall z eps, 0 < eps -> exists del, 0 < del /\
  forall w, Cmod (Cminus w z) < del -> Cmod (Cminus (F w) (F z)) < eps.
Proof.
  intros z eps Heps; destruct (Hhol z) as [d Hd].
  destruct (is_Cderiv_cont F z d Hd eps Heps) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ]; intros w Hw.
  replace (Cminus (F w) (F z)) with (Cminus (F (Cadd z (Cminus w z))) (F z))
    by (replace (Cadd z (Cminus w z)) with w by ring; reflexivity).
  apply Hc; replace (Cminus w z) with (Cminus w z) by ring; exact Hw.
Qed.

(* Goursat: the increment of the primitive is the straight-segment integral *)
Lemma Prim_diff : forall z k,
  seg_int F HF z (Cadd z k) = Cminus (Prim (Cadd z k)) (Prim z).
Proof.
  intros z k; unfold Prim.
  pose proof (goursat F HF Hhol z0 z (Cadd z k)) as HG; unfold tri_int in HG.
  rewrite (seg_reverse F HF z0 (Cadd z k)) in HG.
  assert (HR := f_equal Re HG); assert (HI := f_equal Im HG).
  apply Ceq; unfold Cadd, Copp, Cminus, C0 in *; cbn in *; lra.
Qed.

Theorem Prim_deriv : forall z, is_Cderiv Prim z (F z).
Proof.
  intros z eps Heps.
  destruct (Fcont_pt z (eps / 2) ltac:(lra)) as [del [Hdel Hc]].
  exists del; split; [ exact Hdel | ]; intros k Hk.
  rewrite <- (Prim_diff z k).
  (* F z · k = seg_int (const (F z)) z (z+k) *)
  assert (HFk : Cmul (F z) k = seg_int (fun _ => F z) (CcontC_const (F z)) z (Cadd z k))
    by (rewrite seg_int_const; replace (Cminus (Cadd z k) z) with k by ring; reflexivity).
  rewrite HFk.
  rewrite <- (seg_int_sub F (fun _ => F z) HF (CcontC_const (F z))
              (CcontC_add F (fun _ => Copp (F z)) HF (CcontC_const (Copp (F z))))
              z (Cadd z k)).
  (* ML: Cmod(seg_int (F − F z)) ≤ 2 (eps/2) Cmod k = eps Cmod k *)
  eapply Rle_trans.
  { apply (seg_int_ML (fun w => Cminus (F w) (F z)) _ z (Cadd z k) (eps / 2)).
    intros s Hs.
    assert (Hws : Cmod (Cminus (seg z (Cadd z k) s) z) <= Cmod k).
    { replace (Cminus (seg z (Cadd z k) s) z) with (Cmul (RtoC s) k)
        by (unfold seg, Cadd, Cmul, RtoC, Cminus; apply Ceq; cbn; ring).
      rewrite Cmod_mul, Cmod_RtoC, (Rabs_pos_eq s) by lra.
      apply Rle_trans with (1 * Cmod k);
        [ apply Rmult_le_compat_r; [ apply Cmod_nonneg | lra ] | lra ]. }
    apply Rlt_le, Hc; eapply Rle_lt_trans; [ exact Hws | exact Hk ]. }
  replace (Cminus (Cadd z k) z) with k by ring.
  apply Req_le; lra.
Qed.

(* the loop integral of F over any closed C^1 path is 0 *)
Theorem pathint_loop_holo : forall (gam gam' : R -> C)
  (Hf : Ccont (fun u => Cmul (F (gam u)) (gam' u))) a b,
  a <= b -> gam a = gam b ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Re (gam r)) s (Re (gam' s))) ->
  (forall s, a <= s <= b -> derivable_pt_lim (fun r => Im (gam r)) s (Im (gam' s))) ->
  pathint gam gam' F Hf a b = C0.
Proof.
  intros gam gam' Hf a b Hab Hloop HgR HgI.
  apply (pathint_primitive_loop Prim F gam gam' Hf a b Hab Hloop);
    [ intros s _; apply Prim_deriv | exact HgR | exact HgI ].
Qed.

End Primitive.

Print Assumptions Prim_deriv.
Print Assumptions pathint_loop_holo.

(* ================================================================= *)
(*  END CPrimitive.v  —  primitive of a holomorphic F + loop zero.      *)
(* ================================================================= *)
