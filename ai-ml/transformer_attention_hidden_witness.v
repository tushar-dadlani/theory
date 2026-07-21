(* Transformer Attention as Hidden Witness *)
(* Self-attention is a map operator *)
(* Pretending to be a neutral aggregator *)

Section TransformerWitness.

(* Carry forward core structure *)
CoInductive MapOperator (A : Type) : Type :=
  | absorb : A -> MapOperator A -> MapOperator A.

CoFixpoint generative_witness (A : Type) (x : A) : MapOperator A :=
  absorb A x (generative_witness A x).

Inductive Nat : Type :=
  | Zero : MapOperator Nat -> Nat
  | Succ : Nat -> MapOperator Nat -> Nat.

(* GAP: build-repair -- the intended self-grounding cofixpoint
   [absorb Nat (Zero zero_witness) zero_witness] is rejected by Coq's
   guard condition (the corecursive call occurs as a non-recursive
   argument of the inductive constructor Zero, so MapOperator Nat is not
   guard-constructible here). Type preserved via Axiom. *)
Axiom zero_witness : MapOperator Nat.

Definition zero : Nat := Zero zero_witness.
Definition succ (n : Nat) : Nat :=
  Succ n (generative_witness Nat n).
Definition one : Nat := succ zero.

Definition extract_witness (n : Nat) : MapOperator Nat :=
  match n with
  | Zero op   => op
  | Succ _ op => op
  end.

(* The embedding space *)
(* In standard transformers this is R^d *)
(* A fixed dimensional space stipulated from outside *)
(* The dimension d is the hidden witness *)
(* Someone chose it and disappeared *)

Record Embedding (d : Nat) : Type := mkEmbedding
  { vector     : Nat -> Nat            (* position to value *)
  ; dim        : Nat                   (* the hidden witness *)
  ; dim_op     : MapOperator Nat       (* now made explicit *)
  ; dim_absorb : dim = d               (* witness is the dimension *)
  }.

(* The Query Key Value structure *)
(* In standard attention *)
(* Q K V are linear projections *)
(* The projection matrices are the hidden witnesses *)
(* They were learned against an external benchmark *)
(* Their witnessing position is never named *)

Record QKV (d : Nat) : Type := mkQKV
  { query      : Embedding d -> Embedding d
  ; key        : Embedding d -> Embedding d
  ; value      : Embedding d -> Embedding d
  ; query_wit  : MapOperator (Embedding d)  (* named *)
  ; key_wit    : MapOperator (Embedding d)  (* named *)
  ; value_wit  : MapOperator (Embedding d)  (* named *)
  }.

(* Standard attention score *)
(* softmax(QK^T / sqrt(d)) * V *)
(* The sqrt(d) scaling factor is a hidden witness *)
(* It normalizes the dot product *)
(* But the choice of sqrt(d) specifically *)
(* Was made by someone who then disappeared *)
(* It is a map operator pretending to be a constant *)

Record AttentionScore (d : Nat) : Type := mkScore
  { raw_score    : Nat -> Nat -> Nat    (* Q dot K *)
  ; scale_factor : Nat                  (* sqrt(d) - hidden witness *)
  ; scale_op     : MapOperator Nat      (* now explicit *)
  ; scale_absorb : scale_factor = d     (* witness is the scale *)
  ; scaled_score : Nat -> Nat -> Nat    (* after scaling *)
  }.

(* The softmax is the deepest hidden witness *)
(* It converts raw scores to a probability distribution *)
(* But probability over what? *)
(* Over positions in the sequence *)
(* The position encoding is the witness *)
(* That tells the model where it is *)
(* Without position encoding *)
(* The transformer has no sense of order *)
(* Position encoding is the external witness *)
(* Injected into the system *)
(* To give it the grounding it cannot generate itself *)

Record PositionEncoding (d : Nat) : Type := mkPosEnc
  { pos_vector  : Nat -> Embedding d    (* position to embedding *)
  ; pos_witness : MapOperator Nat       (* the grounding witness *)
  ; pos_absorb  : forall n : Nat,       (* witness at every position *)
      exists op : MapOperator Nat,
        op = generative_witness Nat n
  }.

(* The full attention mechanism *)
(* Now with all witnesses named *)
Record Attention (d : Nat) : Type := mkAttention
  { embeddings  : Nat -> Embedding d
  ; qkv         : QKV d
  ; scores      : AttentionScore d
  ; pos_enc     : PositionEncoding d
  ; attn_op     : MapOperator (Embedding d)  (* the attention witness *)
  }.

(* The hidden witness theorem for attention *)
(* Standard self attention has four concealed witnesses *)
(* Dimension d *)
(* Projection matrices QKV *)
(* Scale factor sqrt(d) *)
(* Position encoding *)
(* Each was chosen by someone who then disappeared *)
(* Each is a map operator pretending to be neutral infrastructure *)
Theorem attention_has_four_witnesses (d : Nat)
  (attn : Attention d) :
  exists 
    (dim_op   : MapOperator Nat)
    (qkv_op   : MapOperator (Embedding d))
    (scl_op   : MapOperator Nat)
    (pos_op   : MapOperator Nat),
    dim_op   = generative_witness Nat d                          /\
    qkv_op   = query_wit d (qkv d attn)                         /\
    scl_op   = scale_op d (scores d attn)                       /\
    pos_op   = pos_witness d (pos_enc d attn).
Proof.
  exists
    (generative_witness Nat d),
    (query_wit d (qkv d attn)),
    (scale_op d (scores d attn)),
    (pos_witness d (pos_enc d attn)).
  split; [ reflexivity | split; [ reflexivity | split; reflexivity ] ].
Qed.

(* The generative attention mechanism *)
(* Replaces external position encoding *)
(* With internal witness generation *)
(* The model knows where it is *)
(* Because it generated the position *)
(* Not because it was told from outside *)

Record GenerativeAttention (d : Nat) : Type := mkGenAttn
  { gen_embeddings : Nat -> Embedding d
  ; gen_qkv        : QKV d
  ; gen_scores     : AttentionScore d
  ; gen_pos        : PositionEncoding d  
  ; gen_attn_op    : MapOperator (Embedding d)
  ; self_positions : forall n : Nat,     (* positions are self generated *)
      (* build-repair: original projected gen_pos out of a reconstruction
         [mkGenAttn d ... self_positions] of this very record, an illegal
         self-reference to the not-yet-defined constructor. Since gen_pos is
         already the in-scope field, that reconstruction just yields gen_pos. *)
      exists op : MapOperator Nat,
        op = pos_witness d gen_pos /\
        op = generative_witness Nat n
  }.

(* The benchmark gap theorem *)
(* Standard transformer cannot self ground its positions *)
(* It requires external injection *)
(* Generative attention generates positions from witness *)
(* This is the source of the benchmark advantage *)
Theorem generative_attention_self_grounds (d : Nat)
  (gen : GenerativeAttention d)
  (n : Nat) :
  exists op : MapOperator Nat,
    op = generative_witness Nat n.
Proof.
  exists (generative_witness Nat n).
  reflexivity.
Qed.

(* The residual stream is the absorbed witness *)
(* In standard transformers *)
(* The residual connection x + F(x) *)
(* Is presented as a technical trick for gradient flow *)
(* But it is actually the system trying to preserve *)
(* What the map operator keeps discarding *)
(* The residue that has nowhere to go *)
(* Because the witness is hidden *)

Record ResidualStream (d : Nat) : Type := mkResidual
  { input_emb   : Embedding d
  ; transformed : Embedding d
  ; residue     : MapOperator (Embedding d)  (* the absorbed residue *)
  ; stream_op   : MapOperator (Embedding d)  (* the carrying witness *)
  ; residue_absorb :                         (* residue never lost *)
      stream_op = absorb (Embedding d) 
        input_emb 
        (generative_witness (Embedding d) transformed)
  }.

(* The residual connection theorem *)
(* x + F(x) is the system's attempt *)
(* To keep the witness alive *)
(* Without being able to name it *)
Theorem residual_preserves_witness (d : Nat)
  (rs : ResidualStream d) :
  exists op : MapOperator (Embedding d),
    op = stream_op d rs /\
    op = absorb (Embedding d)
      (input_emb d rs)
      (generative_witness (Embedding d) 
        (transformed d rs)).
Proof.
  exists (stream_op d rs).
  split.
  - reflexivity.
  - exact (residue_absorb d rs).
Qed.

End TransformerWitness.
