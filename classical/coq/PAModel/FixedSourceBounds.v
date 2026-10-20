(** Calibration for a fixed finite source formula in an arbitrary PA model.
    The source formula and numeral bound are external finite syntax; its
    represented code and the arithmetic model are otherwise arbitrary. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs SetFormulaCodes SetCodeDescent SourceBounded SourceBoundedCalibration
  QuotationFixedSource ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes NumericalTheories.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma fixed_source_numeral_lt_iff M n m :
  coding_lt M (code_numeral M n) (code_numeral M m) <-> n<m.
Proof.
  induction n as [|n IH] in m |- *; destruct m as [|m].
  - split; [intro H;exfalso;exact (coding_not_lt_zero M (zeroM M) H)|lia].
  - split; [lia|intros _;apply coding_zero_lt_succ].
  - split; [intro H;exfalso;exact (coding_not_lt_zero M _ H)|lia].
  - change (coding_lt M (succM M (code_numeral M n))
      (succM M (code_numeral M m)) <-> S n<S m).
    rewrite coding_lt_succ_cancel,IH. lia.
Qed.

#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Theorem fixed_source_bounded_iff {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall M rho f n, code_relation M rho (sf_expression phi) f ->
    (source_bounded M f (code_numeral M n) <-> bounded n phi).
Proof.
  induction phi as [|ff P v|ff op a IHa b IHb|ff q a IH]; intros M rho f n Hf.
  - change (f=zeroM M) in Hf. subst f.
    split; [intros _;constructor|intros _;apply source_bounded_accept_falsity].
  - rewrite sb_atom_bounded. destruct P; cbn [sf_expression] in Hf.
    + apply (proj1 (sf_expression_constructor_graph M rho SFMember (CEconst (sf_index (Vector.hd v))) (CEconst (sf_index (Vector.hd (Vector.tl v))))
        (code_numeral M (sf_index (Vector.hd v)))
        (code_numeral M (sf_index (Vector.hd (Vector.tl v)))) f eq_refl eq_refl)) in Hf.
      rewrite (source_bounded_accept_atom M SFMember _ _ f (code_numeral M n)
        (or_introl eq_refl) Hf). now rewrite !fixed_source_numeral_lt_iff.
    + apply (proj1 (sf_expression_constructor_graph M rho SFEqual (CEconst (sf_index (Vector.hd v))) (CEconst (sf_index (Vector.hd (Vector.tl v))))
        (code_numeral M (sf_index (Vector.hd v)))
        (code_numeral M (sf_index (Vector.hd (Vector.tl v)))) f eq_refl eq_refl)) in Hf.
      rewrite (source_bounded_accept_atom M SFEqual _ _ f (code_numeral M n)
        (or_intror eq_refl) Hf). now rewrite !fixed_source_numeral_lt_iff.
  - destruct (code_relation_total M (sf_expression a) rho) as [x Hx].
    destruct (code_relation_total M (sf_expression b) rho) as [y Hy].
    cbn [sf_expression] in Hf.
    apply (proj1 (sf_expression_constructor_graph M rho _ _ _ x y f Hx Hy)) in Hf.
    assert (Hbinary : sf_binary (match op with Conj=>SFAnd|Disj=>SFOr|Impl=>SFImpl end)).
    { destruct op;unfold sf_binary;auto. }
    rewrite (source_bounded_accept_binary M _ _ _ _ _ Hbinary Hf).
    rewrite (IHa M rho x n Hx),(IHb M rho y n Hy).
    split; [intros [Ha Hb];constructor;assumption|invert_bounds;auto].
  - destruct (code_relation_total M (sf_expression a) rho) as [x Hx].
    cbn [sf_expression] in Hf.
    apply (proj1 (sf_expression_constructor_graph M rho _ _ (CEconst 0)
      x (zeroM M) f Hx eq_refl)) in Hf.
    assert (Hunary : sf_unary (match q with All=>SFAll|Ex=>SFEx end)).
    { destruct q;unfold sf_unary;auto. }
    rewrite (source_bounded_accept_unary M _ _ _ _ Hunary Hf).
    change (source_bounded M x (code_numeral M (S n)) <-> bounded n (quant q a)).
    rewrite (IH M rho x (S n) Hx).
    split; [intro H;constructor;assumption|invert_bounds;assumption].
Qed.

Corollary fixed_source_closed {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) M rho f :
  bounded 0 phi -> code_relation M rho (sf_expression phi) f ->
  source_bounded M f (zeroM M).
Proof. intros Hb Hf. exact (proj2 (fixed_source_bounded_iff phi M rho f 0 Hf) Hb). Qed.

Theorem zfc_source_graph_closed M tag f :
  zfc_source_graph M tag f -> source_bounded M f (zeroM M).
Proof.
  intro Hf. apply (fixed_source_closed (zfc_fixed_source tag) M (fun _=>zeroM M) f).
  - apply zfc_fixed_source_closed.
  - exact Hf.
Qed.

Corollary zfc_fixed_source_theory_closed M f :
  theory_axiom M ZFCFixedSourceTheory f -> source_bounded M f (zeroM M).
Proof.
  rewrite ZFCFixedSourceTheory_axiom. intros [tag Hf].
  exact (zfc_source_graph_closed M tag f Hf).
Qed.


