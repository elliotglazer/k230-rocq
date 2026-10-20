(** Ordinary capture-avoiding substitution transports an internally finite
    PCf conjunction by substituting its explicit ordinal and set names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
  Pairing NumericalContexts NumericalSubstitutionMaps NumericalSubstitution SourcePieceClosure SourcePieceSubstitution
  SourcePieceConjunction SourcePieceConjunctionFormula SourcePieceConjunctionBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_piece_conjunction_substitution_at M n:=forall domain level sb sc d X f rb rc rn base e Y out,
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_piece_table_valid M sb sc n ->source_piece_conjunction M domain level sb sc n d X f ->
  numerical_substitution M f rb rc rn base out ->substitution_lookup M rb rc rn base d e ->
  substitution_lookup M rb rc rn base X Y ->source_piece_conjunction M domain level sb sc n e Y out.
Definition source_piece_conjunction_substitution_formula:form:=
  ∀∀∀∀∀∀∀∀∀∀∀∀∀∀(source_bounded_accept_formula $13(num 1) →source_bounded_accept_formula $12(num 2) →
    source_piece_table_valid_formula $11 $10 $14 →source_piece_conjunction_formula $13 $12 $11 $10 $14 $9 $8 $7 →
    numerical_substitution_formula $7 $6 $5 $4 $3 $0 →substitution_lookup_formula $6 $5 $4 $3 $9 $2 →
    substitution_lookup_formula $6 $5 $4 $3 $8 $1 →source_piece_conjunction_formula $13 $12 $11 $10 $14 $2 $1 $0).
Local Opaque holds source_bounded_accept_formula source_piece_table_valid_formula source_piece_conjunction_formula
  numerical_substitution_formula substitution_lookup_formula.
Lemma source_piece_conjunction_substitution_definable M:Definable1 M(source_piece_conjunction_substitution_at M).
Proof.
  exists source_piece_conjunction_substitution_formula,(fun _=>zeroM M). intro n.
  unfold source_piece_conjunction_substitution_formula,source_piece_conjunction_substitution_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_piece_table_valid_formula_correct.
  setoid_rewrite source_piece_conjunction_formula_correct. setoid_rewrite numerical_substitution_formula_correct.
  setoid_rewrite substitution_lookup_formula_correct. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Theorem source_piece_conjunction_substitution M:forall n,source_piece_conjunction_substitution_at M n.
Proof.
  apply(definable_induction M(source_piece_conjunction_substitution_at M)(source_piece_conjunction_substitution_definable M)).
  - intros domain level sb sc d X f rb rc rn base e Y out HD HL HV HF HR HDE HXY.
    apply source_piece_conjunction_zero in HF.
    destruct(proj1(numerical_substitution_binary M SFImpl(zeroM M)(zeroM M)f rb rc rn base out
      (or_intror(or_intror eq_refl))HF)HR) as(a&b&HA&HB&HImpl).
    apply(proj1(numerical_substitution_invalid M(zeroM M)rb rc rn base a(or_introl eq_refl))) in HA.
    apply(proj1(numerical_substitution_invalid M(zeroM M)rb rc rn base b(or_introl eq_refl))) in HB.
    subst a b. apply source_piece_conjunction_zero. exact HImpl.
  - intros n IH domain level sb sc d X f rb rc rn base e Y out HD HL HV HF HR HDE HXY.
    apply source_piece_conjunction_succ in HF.
    destruct HF as(previous&entry&count&phi&pc&HP&HE&HCount&HPC&HAnd).
    destruct(proj1(numerical_substitution_binary M SFAnd previous pc f rb rc rn base out(or_introl eq_refl)HAnd)HR)
      as(previous'&pc'&HRprevious&HRpc&HAnd').
    pose proof(IH domain level sb sc d X previous rb rc rn base e Y previous' HD HL
      (source_piece_table_valid_prefix M sb sc n HV)HP HRprevious HDE HXY) as HPrevious'.
    assert(HMember:context_member M sb sc(succM M n)entry) by(exists n;split;[apply coding_lt_succ|exact HE]).
    pose proof(source_pc_instance_substitution M domain level count phi d X pc rb rc rn base e Y pc'
      HD HL(HV entry count phi HMember HCount)HPC HRpc HDE HXY) as HPC'.
    apply source_piece_conjunction_succ. exists previous',entry,count,phi,pc'. auto 10.
Qed.

Print Assumptions source_piece_conjunction_substitution.
