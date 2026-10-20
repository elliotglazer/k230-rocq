(** Actual member/equality representation existence for every internally
    coded pair of indices in an arbitrary PA model. Carrier and numeral
    existence are produced by their proved PA-inductive constructions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNumeralLift FixedSourceBounds SourceDefinabilityPrimitives SourceDefinabilityBounds
 SourceRepresentationRecipe SourceRepresentationClosureRecipe SourceRepresentationFalsityClosure
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierClosure SourceEnvironmentCarrierInduction
 SourceNumFClosureRecipe SourceNumFClosureInduction SourceNumFMemberFirst SourceAtomicReverseIndices
 SourceAtomicNamedLaw SourceAtomicCondition SourceAtomicNamedWitnesses SourceAtomicUnaryInstance
 SourceNamedClosureWitnessTotal SourceNamedClosureExistence SourceRepresentativeRenaming
 SourceRepresentationClosureNormalization SourceRepresentationConjunctionCoordinates SourceRepresentationNamedWitness
 SourceNamedQuantifierRules SourceFiniteNameParameters SourceParameterIdentityCalibration SourceNamedDifferenceCertificates
 SourcePropositionalTemplates SourcePropRenaming SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability
 NumericalRenamingMaps NumericalRenaming.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque code_numeral.
Theorem source_zfr_representation_atom M(member:bool)count i j phi out:
 source_bounded M phi count->sf_relation M(if member then SFMember else SFEqual)i j phi->
 source_representation_in_closure_recipe M count phi out->source_zfr_provable M out.
Proof.
 intros BPhi HAtom(rep&succ&closure&targetbody&targetex&middle&HRep&HS&HC&HTB&HTE&HM&HO).
 pose proof(source_representation_recipe_bounded M count phi rep BPhi HRep)as BRep.
 destruct(proj1(source_bounded_accept_atom M(if member then SFMember else SFEqual)i j phi count
  ltac:(destruct member;[exact(or_introl eq_refl)|exact(or_intror eq_refl)])HAtom)BPhi)as(BI&BJ).
 destruct(source_reverse_index_exists M count i BI)as(ki&HI).
 destruct(source_reverse_index_exists M count j BJ)as(kj&HJ).
 destruct(source_zfr_numf_closure_total M ki)as(numI&canI&HNumI&HCanI&PCanI).
 destruct(source_zfr_numf_closure_total M kj)as(numJ&canJ&HNumJ&HCanJ&PCanJ).
 pose proof(source_numf_bound M ki numI HNumI)as BNumI.
 pose proof(source_numf_bound M kj numJ HNumJ)as BNumJ.
 assert(BNumI2:source_bounded M numI(code_numeral M 2))by(exact(source_bounded_monotone M _ _ _ BNumI(proj2(fixed_source_numeral_lt_iff M 1 3)ltac:(lia)))).
 assert(BNumJ2:source_bounded M numJ(code_numeral M 2))by(exact(source_bounded_monotone M _ _ _ BNumJ(proj2(fixed_source_numeral_lt_iff M 1 3)ltac:(lia)))).
 destruct(source_zfr_environment_carrier_total M count)as(carrier&canA&HCarrier&HCanA&PCanA).
 pose proof(source_environment_carrier_recipe_bounded M count carrier HCarrier)as BCarrier.
 destruct(source_zfr_atomic_named_law M member count i j ki kj phi rep carrier numI numJ BPhi HAtom HI HJ HNumI HNumJ HRep HCarrier)
  as(namedA&condition&inner&law&HNamedA&HCondition&HInner&HLaw&PLaw).
 pose proof HCondition as HParts. destruct HParts as(ni&nj&op&nums&HNI&HNJ&HOp&HNums&HCond).
 pose proof(source_unary_instance_representative M numI(code_numeral M 4)ni BNumI HNI)as HNamedI.
 pose proof(source_unary_instance_representative M numJ(code_numeral M 5)nj BNumJ HNJ)as HNamedJ.
 destruct(source_zfr_named_closure_witness_total M carrier canA(code_numeral M 3)namedA BCarrier HCanA PCanA
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 3 3))in H;lia)HNamedA)
  as(memA&ma&ea&outA&HMemA&HMA&HEA&GA&PA).
 assert(memA=AWN_member M 3)by(exact(sf_relation_functional M SFMember(code_numeral M 3)(code_numeral M 2)memA(AWN_member M 3)HMemA(sf_make_numeral M SFMember 3 2))). subst memA.
 destruct(source_environment_carrier_closure_statement_total M numI)as(firstI&HFirstI).
 pose proof(source_zfr_numf_member_first M numI canI firstI HCanI HFirstI PCanI)as PFirstI.
 destruct(source_zfr_named_closure_witness_total M numI firstI(code_numeral M 4)ni BNumI2 HFirstI PFirstI
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 4 3))in H;lia)HNamedI)
  as(memI&mi&ei&outI&HMemI&HMI&HEI&GI&PI).
 assert(memI=AWN_member M 4)by(exact(sf_relation_functional M SFMember(code_numeral M 4)(code_numeral M 2)memI(AWN_member M 4)HMemI(sf_make_numeral M SFMember 4 2))). subst memI.
 destruct(source_environment_carrier_closure_statement_total M numJ)as(firstJ&HFirstJ).
 pose proof(source_zfr_numf_member_first M numJ canJ firstJ HCanJ HFirstJ PCanJ)as PFirstJ.
 destruct(source_zfr_named_closure_witness_total M numJ firstJ(code_numeral M 5)nj BNumJ2 HFirstJ PFirstJ
  ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M 5 3))in H;lia)HNamedJ)
  as(memJ&mj&ej&outJ&HMemJ&HMJ&HEJ&GJ&PJ).
 assert(memJ=AWN_member M 5)by(exact(sf_relation_functional M SFMember(code_numeral M 5)(code_numeral M 2)memJ(AWN_member M 5)HMemJ(sf_make_numeral M SFMember 5 2))). subst memJ.
 destruct(source_zfr_atomic_named_witnesses M member carrier numI numJ namedA ni nj rep condition inner law ea ei ej ma mi mj outA outI outJ
  BCarrier BNumI BNumJ BRep HNamedA HNI HNJ HCondition HInner HLaw PLaw HMA HMI HMJ HEA HEI HEJ GA PA GI PI GJ PJ)
  as(mt&et&namedout&HMT&HET&GNamed&PNamed).
 destruct(source_representation_conjunction_coordinates_total M)as(b&c&HOne&HTwo&HSeven&HNS&HNC).
 assert(ES:succ=code_numeral M(sf_encode source_def_successor01)).
 { exact(code_relation_functional M representation_successor_expression(representation_identity_environment M)succ _ HS
   (source_parameter_identity_calibration M source_def_successor01(source_finite_parameter_names 3)
    (representation_identity_environment M)(representation_identity_names_graph M))). }
 assert(EC:closure=code_numeral M(sf_encode representation_closure_condition)).
 { exact(code_relation_functional M representation_closure_expression(representation_identity_environment M)closure _ HC
   (source_parameter_identity_calibration M representation_closure_condition(source_finite_parameter_names 3)
    (representation_identity_environment M)(representation_identity_names_graph M))). }
 assert(HSLift:numerical_renaming M(code_numeral M(sf_encode named_difference_successor))b c(code_numeral M 8)(zeroM M)succ)by(now rewrite ES).
 assert(HCLift:numerical_renaming M(code_numeral M(sf_encode named_difference_closure))b c(code_numeral M 8)(zeroM M)closure)by(now rewrite EC).
 pose proof(source_named_representation_exists_rename M rep mt et targetbody targetex b c(code_numeral M 8)(zeroM M)
  BRep HMT HET HOne HTwo HTB HTE)as HETLift.
 set(values:=NCE_values M succ closure targetex).
 assert(GOut:code_relation M values(source_prop_expression NCE_template)out).
 { apply(source_prop_template_join M values SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2))succ middle out eq_refl);[|exact HO].
   exact(source_prop_template_join M values SFImpl(SPTSlot 1)(SPTSlot 2)closure targetex middle eq_refl eq_refl HM). }
 assert(HRename:numerical_renaming M namedout b c(code_numeral M 8)(zeroM M)out).
 { apply(source_prop_renaming M(named_closure_values M et)values b c(code_numeral M 8)(zeroM M)NCE_template namedout out);[|exact GNamed|exact GOut].
   cbn[source_prop_slots NCE_template named_closure_values NCE_values values]. exact(conj HSLift(conj HCLift HETLift)). }
 apply(proj1(source_zfr_descriptor_provable M out)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor namedout b c(code_numeral M 8)(zeroM M)out
  (proj2(source_zfr_descriptor_provable M namedout)PNamed)HRename).
Qed.
Print Assumptions source_zfr_representation_atom.
