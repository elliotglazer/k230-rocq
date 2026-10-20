(** The PA-definable uniform TV induction predicate. All source formulas,
    contexts, carrier names, parameter counts and proof codes are internal. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceRelativization SourceSetRelativization
  SourceIffGraphs SourceTarskiVaughtInputs SourcePropositionalTemplates SourceFunctionalityShells SetSchemaConstructors.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.

Definition source_tv_at M phi:=forall domain count carrier left right equiv cb cc cn k,
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
  context_bounded M cb cc cn k ->coding_lt M count(succM M k) ->coding_lt M carrier k ->
  source_relativization M domain phi left ->source_set_relativization M carrier phi right ->
  source_iff_graph M left right equiv ->source_tv_members M cb cc cn count carrier ->
  source_tv_witnesses M domain phi count carrier cb cc cn ->source_tv_containment M domain carrier cb cc cn ->
  source_full_prv M cb cc cn equiv.
Definition source_tv_at_formula:form:=∀∀∀∀∀∀∀∀∀∀(
  source_bounded_accept_formula $9(num 1) →source_bounded_accept_formula $10 $8 →
  context_bounded_formula $3 $2 $1 $0 →Peano.sless $8(σ $0) →Peano.sless $7 $0 →
  source_relativization_formula $9 $10 $6 →source_set_relativization_formula $7 $10 $5 →
  source_iff_formula $6 $5 $4 →source_tv_members_formula $3 $2 $1 $8 $7 →
  source_tv_witnesses_formula $9 $10 $8 $7 $3 $2 $1 →source_tv_containment_formula $9 $7 $3 $2 $1 →
  source_full_prv_formula $3 $2 $1 $4).
Local Opaque holds source_bounded_accept_formula context_bounded_formula Peano.sless
  source_relativization_formula source_set_relativization_formula source_iff_formula
  source_tv_members_formula source_tv_witnesses_formula source_tv_containment_formula source_full_prv_formula.
Theorem source_tv_at_definable M:Definable1 M(source_tv_at M).
Proof.
  exists source_tv_at_formula,(fun _=>zeroM M). intro phi.
  unfold source_tv_at_formula,source_tv_at. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite context_bounded_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite source_relativization_formula_correct. setoid_rewrite source_set_relativization_formula_correct.
  setoid_rewrite source_iff_formula_correct. setoid_rewrite source_tv_members_formula_correct.
  setoid_rewrite source_tv_witnesses_formula_correct. setoid_rewrite source_tv_containment_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_full_iff_reflexive M cb cc cn a equiv k:
  context_bounded M cb cc cn k ->source_bounded M a k ->source_iff_graph M a a equiv ->
  source_full_prv M cb cc cn equiv.
Proof.
  intros BC BA HE.
  assert(P:source_prop_program nil(SPTAnd(SPTImpl(SPTSlot 0)(SPTSlot 0))(SPTImpl(SPTSlot 0)(SPTSlot 0)))).
  { apply SPTCI;apply SPTII;apply SPTCtx;cbn;auto. }
  apply(source_prop_program_sound M _ _ P(fun _=>a)k cb cc cn equiv);[intro;exact BA|exact BC| |].
  - intros p H f HF. contradiction.
  - destruct(source_iff_parts M a a equiv HE)as(lr&rl&HL&HR&HO).
    eapply(source_prop_template_join M(fun _=>a)SFAnd
      (SPTImpl(SPTSlot 0)(SPTSlot 0))(SPTImpl(SPTSlot 0)(SPTSlot 0))lr rl equiv).
    + exact(source_prop_template_join M(fun _=>a)SFImpl(SPTSlot 0)(SPTSlot 0)a a lr eq_refl eq_refl HL).
    + exact(source_prop_template_join M(fun _=>a)SFImpl(SPTSlot 0)(SPTSlot 0)a a rl eq_refl eq_refl HR).
    + exact HO.
Qed.
Print Assumptions source_tv_at_definable.
Print Assumptions source_full_iff_reflexive.
