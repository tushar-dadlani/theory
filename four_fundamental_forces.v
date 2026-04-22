(* Forces emerge from the tower levels.
   Each level introduces a new geometric constraint.
   That constraint IS the force. *)

(* Level 3 = FLAT = no force yet, just structure *)
Theorem level3_no_force :
  forall a b c : Sym3,
    field3 (field3 a b) c = field3 a (field3 b c).
Proof. intros a b c; destruct a, b, c; reflexivity. Qed.

(* Level 5 = CURVED = force appears as non-associativity *)
Theorem force_is_curvature :
  metric5 (metric5 X H) O <> metric5 X (metric5 H O).
Proof. simpl. discriminate. Qed.

(* Gravity = F-axis absorption = the singularity of the metric *)
Theorem gravity_absorbs :
  forall s : Sym5, metric5 M s = M.
Proof. intro s; destruct s; reflexivity. Qed.

(* Mass gap = minimum force quantum = 1 tower step *)
Theorem force_quantum :
  has_mass_gap (fun _ => 1) 1.
Proof.
  unfold has_mass_gap. split; [lia | intros; lia].
Qed.
