(** Calibration to actual source syntax, and internal closure under an
    arbitrary model-valued universal prefix. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs StandardModel SetFormulaCodes SetCodeDescent SourceBounded NumericalSetClosure.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition sb_prefix_property M n := forall body result k,
  all_prefix M n body result ->
  (source_bounded M result k <-> source_bounded M body (addM M n k)).
Definition sb_prefix_property_formula : form :=
  ∀∀∀ (all_prefix_formula $3 $2 $1 →
    ((source_bounded_accept_formula $1 $0 → source_bounded_accept_formula $2 ($3 ⊕ $0)) ∧
     (source_bounded_accept_formula $2 ($3 ⊕ $0) → source_bounded_accept_formula $1 $0))).

Local Opaque holds all_prefix_formula source_bounded_accept_formula.
Lemma sb_prefix_property_definable M : Definable1 M (sb_prefix_property M).
Proof.
  exists sb_prefix_property_formula,(fun _ => zeroM M). intro n.
  unfold sb_prefix_property_formula,sb_prefix_property.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_and. repeat setoid_rewrite holds_imp.
  setoid_rewrite all_prefix_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. reflexivity.
Qed.

Theorem all_prefix_bounded M n : sb_prefix_property M n.
Proof.
  apply (definable_induction M (sb_prefix_property M)).
  - apply sb_prefix_property_definable.
  - intros body result k H. apply all_prefix_zero in H. subst result.
    rewrite (Arithmetic.add_zero M k). reflexivity.
  - intros j IH body result k H.
    apply all_prefix_succ in H. destruct H as [previous [Hp Hr]].
    rewrite (source_bounded_accept_unary M SFAll previous result k (or_introl eq_refl) Hr).
    rewrite (IH body previous (succM M k) Hp).
    replace (addM M j (succM M k)) with (addM M (succM M j) k); [reflexivity|].
    rewrite (Arithmetic.add_comm M j (succM M k)), !Arithmetic.add_succ.
    now rewrite (Arithmetic.add_comm M k j).
Qed.

Corollary all_prefix_closed_iff M n body result : all_prefix M n body result ->
  (source_bounded M result (zeroM M) <-> source_bounded M body n).
Proof.
  intro H. rewrite (all_prefix_bounded M n body result (zeroM M) H).
  rewrite (Arithmetic.add_comm M n (zeroM M)), (Arithmetic.add_zero M n). reflexivity.
Qed.

Corollary all_prefix_closes M n body result :
  source_bounded M body n -> all_prefix M n body result -> source_bounded M result (zeroM M).
Proof. intros Hb Hp. apply (proj2 (all_prefix_closed_iff M n body result Hp)). exact Hb. Qed.

Lemma sb_source_constructor_nat h a b : sf_relation natModel h a b (sf_make h a b).
Proof. unfold sf_relation,sf_make. rewrite code_relation_natModel. reflexivity. Qed.

Lemma sb_coding_lt_nat a b : coding_lt natModel a b <-> a<b.
Proof.
  change ((exists d, b=S (a+d)) <-> a<b). split.
  - intros [d H]. lia.
  - intro H. exists (b-S a). lia.
Qed.

Lemma sb_vector_two {A} (v : Vector.t A 2) :
  v = Vector.cons A (Vector.hd v) 1
    (Vector.cons A (Vector.hd (Vector.tl v)) 0 (Vector.nil A)).
Proof. rewrite (Vector.eta v). f_equal. rewrite (Vector.eta (Vector.tl v)). f_equal. apply Vector.nil_spec. Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Lemma sb_term_bounded k (t : sf_term) : bounded_t k t <-> sf_index t < k.
Proof.
  destruct t as [i|f v]; [|destruct f]. cbn [sf_index].
  split; [intro H; inversion H; assumption|intro H;constructor;assumption].
Qed.

Lemma sb_atom_bounded {ff} k P (v : Vector.t sf_term (ZF_pred_ar P)) :
  @bounded sig_empty ZFSignature.ZF_pred_sig full_operators ff k (atom P v) <->
  sf_index (Vector.hd v)<k /\ sf_index (Vector.hd (Vector.tl v))<k.
Proof.
  destruct P; rewrite (sb_vector_two v); cbn [Vector.hd Vector.tl].
  all: split.
  all: try (intro H; revert H; invert_bounds;
    match goal with Hargs : forall _, Vector.In _ _ -> _ |- _ =>
      split; apply sb_term_bounded; apply Hargs; [constructor|constructor 2;constructor]
    end).
  all: intros [Hx Hy]; constructor; intros t Ht;
    apply Vector.In_cons_iff in Ht as [<-|Ht]; [now apply sb_term_bounded|];
    apply Vector.In_cons_iff in Ht as [<-|Ht]; [now apply sb_term_bounded|]; inversion Ht.
Qed.

Theorem source_bounded_sf_encode {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall k, source_bounded natModel (sf_encode phi) k <-> bounded k phi.
Proof.
  induction phi as [|ff P v|ff op a IHa b IHb|ff q a IH]; intro k.
  - split; [intros _;constructor|intros _;apply source_bounded_accept_falsity].
  - rewrite sb_atom_bounded. destruct P; cbn [sf_encode].

    + rewrite (source_bounded_accept_atom natModel SFMember _ _ _ k
        (or_introl eq_refl) (sb_source_constructor_nat _ _ _)).
      now rewrite !sb_coding_lt_nat.
    + rewrite (source_bounded_accept_atom natModel SFEqual _ _ _ k
        (or_intror eq_refl) (sb_source_constructor_nat _ _ _)).
      now rewrite !sb_coding_lt_nat.
  - cbn [sf_encode].
    assert (Hbinary : sf_binary (match op with Conj=>SFAnd|Disj=>SFOr|Impl=>SFImpl end)).
    { destruct op; unfold sf_binary; auto. }
    rewrite (source_bounded_accept_binary natModel _ _ _ _ k Hbinary (sb_source_constructor_nat _ _ _)).
    rewrite IHa,IHb. split; [intros [Ha Hb];constructor;assumption|intro H;revert H;invert_bounds;auto].
  - cbn [sf_encode].
    assert (Hunary : sf_unary (match q with All=>SFAll|Ex=>SFEx end)).
    { destruct q; unfold sf_unary; auto. }
    rewrite (source_bounded_accept_unary natModel _ _ _ k Hunary (sb_source_constructor_nat _ _ _)).
    change (source_bounded natModel (sf_encode a) (S k) <-> bounded k (quant q a)).
    rewrite IH. split; [intro H;constructor;assumption|intro H;revert H;invert_bounds;assumption].
Qed.






