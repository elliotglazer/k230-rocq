(** Actual ZFR monotonicity for internally finite PCf conjunctions. Each
    piece law and each finite common proof context is constructed internally. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  Pairing SetFormulaCodes SourceBounded NumericalContexts NumericalInstantiation SourceDomainInstances
  SourceOrdinalPredicate SourceRawSubset SourceRawSubsetBounds SourceHierarchySyntax SourceThreeConditions
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionFormula SourcePieceConjunctionBounds
  SourcePieceMonotonicity SourcePieceLawFormulas SourcePiecePrograms SourcePropositionalTemplates
  SourceWitnessProofComposition SourceFunctionalityShells SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_ordinal_predicate_code.

Lemma source_piece_curried_total M a b c d e:exists law,source_three_curried M a b c d e law.
Proof.
  destruct(sf_relation_total M SFImpl d e) as(de&HDE).
  destruct(sf_relation_total M SFImpl c de) as(cde&HCD).
  destruct(sf_relation_total M SFImpl b cde) as(bcde&HBC).
  destruct(sf_relation_total M SFImpl a bcde) as(law&HL).
  exists law,de,cde,bcde. auto.
Qed.

Definition source_piece_conjunction_mono_at M domain level n:=forall sb sc d e X od oe subset old new law k,
  source_piece_table_valid M sb sc n ->coding_lt M d k ->coding_lt M e k ->coding_lt M X k ->
  numerical_instantiation M(source_ordinal_predicate_code M)d od ->
  numerical_instantiation M(source_ordinal_predicate_code M)e oe ->source_raw_subset_graph M d e subset ->
  source_piece_conjunction M domain level sb sc n d X old ->source_piece_conjunction M domain level sb sc n e X new ->
  source_three_curried M od oe subset old new law ->source_descriptor_provable M ZFRSourceDescriptor law.
Definition source_piece_conjunction_mono_formula:form:=
  ∀∀∀∀∀∀∀∀∀∀∀∀(source_piece_table_valid_formula $11 $10 $12 →
    Peano.sless $9 $0 →Peano.sless $8 $0 →Peano.sless $7 $0 →
    numerical_instantiation_formula(num(sf_encode source_ordinal_predicate))$9 $6 →
    numerical_instantiation_formula(num(sf_encode source_ordinal_predicate))$8 $5 →source_piece_subset_formula $9 $8 $4 →
    source_piece_conjunction_formula $13 $14 $11 $10 $12 $9 $7 $3 →
    source_piece_conjunction_formula $13 $14 $11 $10 $12 $8 $7 $2 →
    source_piece_curried_formula $6 $5 $4 $3 $2 $1 →source_descriptor_provable_formula ZFRSourceDescriptor $1).
Local Opaque holds source_piece_table_valid_formula Peano.sless numerical_instantiation_formula source_piece_subset_formula
  source_piece_conjunction_formula source_piece_curried_formula source_descriptor_provable_formula.
Lemma source_piece_conjunction_mono_definable M domain level:Definable1 M(source_piece_conjunction_mono_at M domain level).
Proof.
  exists source_piece_conjunction_mono_formula,(domain.:level.:fun _=>zeroM M). intro n.
  unfold source_piece_conjunction_mono_formula,source_piece_conjunction_mono_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_piece_table_valid_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite source_piece_subset_formula_correct.
  setoid_rewrite source_piece_conjunction_formula_correct. setoid_rewrite source_piece_curried_formula_correct.
  setoid_rewrite source_descriptor_provable_formula_correct. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Definition source_piece_seven_environment{A}(od oe subset pd pe cd ce:A)i:=
  match i with 0=>od|1=>oe|2=>subset|3=>pd|4=>pe|5=>cd|_=>ce end.

Theorem source_zfr_piece_conjunction_monotonicity M domain level:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  forall n,source_piece_conjunction_mono_at M domain level n.
Proof.
  intros HD HLevel.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  apply(definable_induction M(source_piece_conjunction_mono_at M domain level)
    (source_piece_conjunction_mono_definable M domain level)).
  - intros sb sc d e X od oe subset old new law k HV HDk HEk HXk HOD HOE HS HOld HNew HLaw.
    pose proof(source_piece_conjunction_bounded M(zeroM M)domain level sb sc d X old k HD HL HV HDk HXk HOld) as BOld.
    apply source_piece_conjunction_zero in HOld,HNew.
    pose proof(sf_relation_functional M SFImpl(zeroM M)(zeroM M)new old HNew HOld) as E. subst new.
    pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d od k(source_ordinal_predicate_bounded M)HDk HOD) as BOD.
    pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)e oe k(source_ordinal_predicate_bounded M)HEk HOE) as BOE.
    pose proof(source_raw_subset_bounded M d e subset k HDk HEk HS) as BS.
    apply(proj2(source_zfr_descriptor_provable M law)).
    apply(source_piece_prop_zero M _ source_piece_mono_identity_program
      (fun (idx:nat) =>match idx with 0=>od|1=>oe|2=>subset|_=>old end)k law).
    + intros[|[|[|i]]];assumption.
    + exact(source_three_curried_code M od oe subset old old law HLaw).
  - intros n IH sb sc d e X od oe subset old new law k HV HDk HEk HXk HOD HOE HS HOld HNew HLaw.
    apply source_piece_conjunction_succ in HOld,HNew.
    destruct HOld as(pd&entry&count&phi&cd&HPD&HEntry&HCount&HCD&HAndD).
    destruct HNew as(pe&entry'&count'&phi'&ce&HPE&HEntry'&HCount'&HCE&HAndE).
    pose proof(beta_unique M sb sc n entry' entry HEntry' HEntry) as E. subst entry'.
    destruct(pair_injective M entry count' phi' count phi HCount' HCount) as[E E']. subst count' phi'.
    pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
    assert(HMember:context_member M sb sc(succM M n)entry) by(exists n;split;[apply coding_lt_succ|exact HEntry]).
    pose proof(HV entry count phi HMember HCount) as HB.
    destruct(source_piece_curried_total M od oe subset pd pe) as(prevLaw&HPrevLaw).
    pose proof(IH sb sc d e X od oe subset pd pe prevLaw k HPrefix HDk HEk HXk HOD HOE HS HPD HPE HPrevLaw) as PPrev.
    destruct(source_piece_curried_total M od oe subset cd ce) as(pieceLaw&HPieceLaw).
    pose proof(source_zfr_pc_monotonicity M domain level count phi d e X od oe subset cd ce pieceLaw
      HD HB HLevel HOD HOE HS HCD HCE HPieceLaw) as PPiece.
    pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d od k(source_ordinal_predicate_bounded M)HDk HOD) as BOD.
    pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)e oe k(source_ordinal_predicate_bounded M)HEk HOE) as BOE.
    pose proof(source_raw_subset_bounded M d e subset k HDk HEk HS) as BS.
    pose proof(source_piece_conjunction_bounded M n domain level sb sc d X pd k HD HL HPrefix HDk HXk HPD) as BPD.
    pose proof(source_piece_conjunction_bounded M n domain level sb sc e X pe k HD HL HPrefix HEk HXk HPE) as BPE.
    pose proof(source_pc_instance_bounded M domain level count phi d X cd k HD HL HB HDk HXk HCD) as BCD.
    pose proof(source_pc_instance_bounded M domain level count phi e X ce k HD HL HB HEk HXk HCE) as BCE.
    set(rho:=source_piece_seven_environment od oe subset pd pe cd ce).
    assert(HEnv:forall i,source_bounded M(rho i)k).
    { intros[|[|[|[|[|[|i]]]]]];cbn[rho source_piece_seven_environment];assumption. }
    apply(proj2(source_zfr_descriptor_provable M law)).
    apply(source_zfr_prop_two M _ _ _ source_piece_conjunction_mono_program rho k prevLaw pieceLaw law HEnv).
    + destruct HPrevLaw as(a&b&c&HA&HB'&HC&HD'). unfold source_piece_curried_template,source_prop_expression.
      functionality_graph.
    + destruct HPieceLaw as(a&b&c&HA&HB'&HC&HD'). unfold source_piece_curried_template,source_prop_expression.
      functionality_graph.
    + destruct HLaw as(a&b&c&HA&HB'&HC&HD'). unfold source_piece_curried_template,source_prop_expression.
      functionality_graph.
    + exact(proj1(source_zfr_descriptor_provable M prevLaw)PPrev).
    + exact PPiece.
Qed.

Print Assumptions source_zfr_piece_conjunction_monotonicity.
