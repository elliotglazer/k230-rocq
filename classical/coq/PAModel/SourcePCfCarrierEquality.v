(** PA-definable proof production for equality transport of an internally
    finite PCf conjunction. Every piece law is an actual ZFR deduction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  Pairing SetFormulaCodes SourceBounded NumericalContexts SourceHierarchySyntax
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionFormula SourcePieceConjunctionBounds
  SourcePieceCarrierEquality SourcePCfCarrierProgram SourcePCfCarrierInvariant SourcePropositionalTemplates SourceFunctionalityShells
  SourceConditionalIdentity SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceWitnessProofComposition.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_zfr_pcf_carrier_equality_all M domain level:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  forall n,source_pcf_carrier_equality_at M domain level n.
Proof.
  intros HD HLevel.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
  apply(definable_induction M(source_pcf_carrier_equality_at M domain level)
    (source_pcf_carrier_equality_definable M domain level)).
  - intros sb sc d X Y equal old new map law k HV HDk HXk HYk HEq HOld HNew HMap HLaw.
    pose proof(source_piece_conjunction_bounded M(zeroM M)domain level sb sc d X old k HD HL HV HDk HXk HOld)as BOld.
    apply source_piece_conjunction_zero in HOld,HNew.
    pose proof(sf_relation_functional M SFImpl(zeroM M)(zeroM M)new old HNew HOld)as E. subst new.
    assert(BEqual:source_bounded M equal k).
    { exact(proj2(source_bounded_accept_atom M SFEqual X Y equal k(or_intror eq_refl)HEq)(conj HXk HYk)). }
    apply(proj1(source_zfr_descriptor_provable M law)).
    exact(source_descriptor_conditional_identity M ZFRSourceDescriptor equal old map law k BEqual BOld HMap HLaw).
  - intros n IH sb sc d X Y equal old new map law k HV HDk HXk HYk HEq HOld HNew HMap HLaw.
    apply source_piece_conjunction_succ in HOld,HNew.
    destruct HOld as(pd&entry&count&phi&cd&HPD&HEntry&HCount&HCD&HAndD).
    destruct HNew as(pe&entry'&count'&phi'&ce&HPE&HEntry'&HCount'&HCE&HAndE).
    pose proof(beta_unique M sb sc n entry' entry HEntry' HEntry)as E. subst entry'.
    destruct(pair_injective M entry count' phi' count phi HCount' HCount)as[E E']. subst count' phi'.
    pose proof(source_piece_table_valid_prefix M sb sc n HV)as HPrefix.
    assert(HMember:context_member M sb sc(succM M n)entry)by(exists n;split;[apply coding_lt_succ|exact HEntry]).
    pose proof(HV entry count phi HMember HCount)as HPhi.
    destruct(sf_relation_total M SFImpl pd pe)as(prevMap&HPrevMap).
    destruct(sf_relation_total M SFImpl equal prevMap)as(prevLaw&HPrevLaw).
    pose proof(IH sb sc d X Y equal pd pe prevMap prevLaw k HPrefix HDk HXk HYk HEq HPD HPE HPrevMap HPrevLaw)as PPrev.
    destruct(sf_relation_total M SFImpl cd ce)as(pieceMap&HPieceMap).
    destruct(sf_relation_total M SFImpl equal pieceMap)as(pieceLaw&HPieceLaw).
    pose proof(source_zfr_pc_carrier_equality M domain level count phi d X Y equal cd ce pieceMap pieceLaw
      HD HPhi HLevel HEq HCD HCE HPieceMap HPieceLaw)as PPiece.
    assert(BEqual:source_bounded M equal k).
    { exact(proj2(source_bounded_accept_atom M SFEqual X Y equal k(or_intror eq_refl)HEq)(conj HXk HYk)). }
    pose proof(source_piece_conjunction_bounded M n domain level sb sc d X pd k HD HL HPrefix HDk HXk HPD)as BPD.
    pose proof(source_piece_conjunction_bounded M n domain level sb sc d Y pe k HD HL HPrefix HDk HYk HPE)as BPE.
    pose proof(source_pc_instance_bounded M domain level count phi d X cd k HD HL HPhi HDk HXk HCD)as BCD.
    pose proof(source_pc_instance_bounded M domain level count phi d Y ce k HD HL HPhi HDk HYk HCE)as BCE.
    set(rho:=source_pcf_carrier_environment equal pd pe cd ce).
    assert(HRho:forall i,source_bounded M(rho i)k).
    { intros[|[|[|[|[|i]]]]];unfold rho,source_pcf_carrier_environment;assumption. }
    apply(source_zfr_prop_two M pcf_carrier_previous pcf_carrier_piece pcf_carrier_conjunction
      source_pcf_carrier_conjunction_program rho k prevLaw pieceLaw law HRho).
    + unfold rho,source_pcf_carrier_environment,source_prop_expression,pcf_carrier_previous. functionality_graph.
    + unfold rho,source_pcf_carrier_environment,source_prop_expression,pcf_carrier_piece. functionality_graph.
    + unfold rho,source_pcf_carrier_environment,source_prop_expression,pcf_carrier_conjunction. functionality_graph.
    + exact PPrev.
    + exact PPiece.
Qed.

Print Assumptions source_zfr_pcf_carrier_equality_all.
