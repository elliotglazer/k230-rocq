(** Actual selected-set profile for an arbitrary represented source matrix.
    Both Op5 and SC correctness are derived from genuine source proofs in
    the included finite ZFR context; no profile/correctness premise remains. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityBounds SourceDefinabilityStep NumericalEnvironments NumericalSubstitution
 NumericalSourceFull SourceRoleReopening SourceRepresentationRecipe SourceEnvInClosureConstructor
 SourceDnEliminationInvariant SourceSetRelativization SourceIffGraphs NumericalContexts SourceNamedVacuity
 SourceSelectionSCBinder SourceLocalDefinabilityContext SourceSelectionRepresentationGuard
 SourceSelectionOperationGraph SourceLocalSelectionOperationUse SourceSelectionProfileLogic
 SourcePropositionalTemplates SourceRepresentationDifferenceProgram SourceBooleanIffPrograms.
Unset Implicit Arguments.
Definition local_selection_profile_values M inSelected inCarrier selection matrix i:=match i with
 |0=>inSelected|1=>inCarrier|2=>selection|3=>matrix|_=>zeroM M end.
From PAModel Require Import SourceLocalSelectionProfilePoint SourceNamedQuantifierRules SourceNamedVacuity.
From PAModel Require Import SourceLocalSelectionProfileAll SourceLocalSelectedSubset
 SourceLocalDefinabilityAccess SourceUpperProofHelpers.
From PAModel Require Import SourceLocalSelectedDefProfile SourceLocalSelectionExists SourceLocalSelectionExistsGraph
 SourceLocalDefinabilityContent SourceNamedElimination SourceContextProofHelpers SourceConjunctionRules
 SourceProofWeakening NumericalEnvironments SourceUpperProofHelpers SourceDerivedRules.
From PAModel Require Import SourceLocalSelectedDefProfileExists SourceLocalAssignedEnvExistence
 SourceEnvInClosureRecipe SourceLocalNamedClosureExistence SourceRepresentationClosureRecipe SourceZFRProvability.
From PAModel Require Import SourceLocalDefProfileEnvExists SourceLocalRepresentationExists SourceRepresentationClosureRecipe.
From PAModel Require Import SourceLocalDefProfileRepExists SourceLocalDefinabilityUnpack SourceLocalDefinabilityContent
 SourceLocalNamedExistsImplication SourceFiniteParameters SourceFiniteNameParameters.
Theorem source_full_local_definability_from_data M count phi rep d X rb rc assignedRep pb pc value vb vc
 environment next old ob oc previous new nb nc target0 extension memberValue memberResult relative assignedPhi result
 fb fc fn gb gc gn k sc final guard selected operation inSelected rawPair rawProfile newPair profile allProfile
 closure definables selectedInClosure subset selectedInDef accessTail accessPoint accessAll subsetPoint profileBody target
 successor succ closureCode repInClosure oldInClosure sourceBody sourceEx
 envClosure envBody envEx repClosure repBody repEx predicate contentPair content:
 source_bounded M phi(succM M count) ->source_representation_recipe M(succM M count)phi rep ->
 source_role_reopening M X d rb rc ->
 numerical_substitution M rep rb rc(code_numeral M 2)(code_numeral M 2)assignedRep ->
 source_envf M count environment ->source_envf M(succM M count)next ->source_def_step M true environment next ->
 environment_cons M pb pc count value vb vc(succM M count) ->
 environment_cons M pb pc count old ob oc(succM M count) ->
 environment_cons M vb vc(succM M count)new nb nc(succM M(succM M count)) ->
 numerical_substitution M environment ob oc(succM M count)(zeroM M)previous ->
 numerical_substitution M next nb nc(succM M(succM M count))(zeroM M)target0 ->
 code_relation M(EIC_ext_roles old new value)EIC_ext_expression extension ->
 old<>new ->value<>old ->(forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old) ->
 numerical_substitution M phi vb vc(succM M count)(zeroM M)assignedPhi ->
 source_set_relativization M X assignedPhi relative ->source_bounded M relative k ->
 sf_relation M SFMember value X memberValue ->sf_relation M SFMember new d memberResult ->
 source_iff_graph M memberResult relative result ->
 source_dn_parameter_proofs M count pb pc X gb gc gn ->
 
 source_named_context_vacuous M gb gc gn new ->context_bounded M gb gc gn k ->
 source_bounded M extension k ->source_bounded M memberResult k ->source_bounded M memberValue k ->
 source_named_vacuous M new relative ->
 new<>value ->new<>X ->new<>d ->
 code_relation M(local_SC_names d old value)source_local_SC_expression sc ->
 source_iff_graph M sc relative final ->source_local_fixed_context M fb fc fn ->
 context_included M fb fc fn gb gc gn ->sf_relation M SFImpl memberValue final guard ->
 code_relation M(local_operation5_names d old X selected)source_local_operation5_expression operation ->
 sf_relation M SFMember value selected inSelected ->source_bounded M inSelected k ->source_bounded M sc k ->
 sf_relation M SFAnd memberValue sc rawPair ->source_iff_graph M inSelected rawPair rawProfile ->
 sf_relation M SFAnd memberValue relative newPair ->source_iff_graph M inSelected newPair profile ->
 
 source_named_context_vacuous M gb gc gn value ->source_named_quantifier M true value profile allProfile ->
 value<>selected ->value<>X ->selected<>closure ->selected<>X ->selected<>definables ->
 sf_relation M SFMember selected closure selectedInClosure ->
 code_relation M(local_subset_names selected X)source_local_subset_expression subset ->
 sf_relation M SFMember selected definables selectedInDef ->sf_relation M SFImpl subset selectedInDef accessTail ->
 sf_relation M SFImpl selectedInClosure accessTail accessPoint ->source_bounded M accessPoint k ->
 code_relation M(local_access_names closure X definables)source_local_access_expression accessAll ->
 sf_relation M SFImpl inSelected memberValue subsetPoint ->
 sf_relation M SFAnd selectedInDef allProfile profileBody ->source_named_quantifier M false selected profileBody target ->
 source_named_context_vacuous M gb gc gn selected ->
 source_named_vacuous M new sourceBody ->source_named_vacuous M value sourceBody ->
 source_bounded M sourceBody k ->source_bounded M profileBody k ->
 code_relation M(local_subset_names X successor)source_local_successor_expression succ ->
 code_relation M(local_subset_names successor closure)source_local_closure_expression closureCode ->
 sf_relation M SFMember d closure repInClosure ->sf_relation M SFMember old closure oldInClosure ->
 (forall i,(i<6)%nat ->selected<>local_selection_exists_roles X successor closure d old i) ->
 sf_relation M SFAnd selectedInClosure operation sourceBody ->
 code_relation M(local_selection_exists_roles X successor closure d old)source_local_selection_exists_expression sourceEx ->
 
 source_representation_in_closure_recipe M(succM M count)phi repClosure ->source_full_prv M fb fc fn repClosure ->
 d<>X ->d<>closure ->sf_relation M SFAnd repInClosure assignedRep repBody ->source_named_quantifier M false d repBody repEx ->
 source_named_context_vacuous M gb gc gn d ->source_named_vacuous M d target ->
 source_named_vacuous M new repBody ->source_named_vacuous M value repBody ->
 source_named_vacuous M selected repBody ->source_named_vacuous M old repBody ->source_bounded M repBody k ->source_env_in_closure_recipe M count environment envClosure ->source_full_prv M fb fc fn envClosure ->
 old<>closure ->sf_relation M SFAnd previous oldInClosure envBody ->source_named_quantifier M false old envBody envEx ->
 source_named_context_vacuous M gb gc gn old ->source_named_vacuous M old target ->
 source_named_vacuous M new envBody ->source_named_vacuous M value envBody ->source_named_vacuous M selected envBody ->
 source_bounded M envBody k ->
 code_relation M(local_closure_roles X successor closure)representation_successor_expression succ ->
 code_relation M(local_closure_roles X successor closure)representation_closure_expression closureCode ->
 code_relation M(local_def_names X definables)source_local_def_predicate_expression predicate ->
 sf_relation M SFAnd succ closureCode contentPair ->sf_relation M SFAnd contentPair accessAll content ->
 closure<>successor ->closure<>X ->closure<>definables ->successor<>X ->successor<>definables ->
 source_named_context_vacuous M gb gc gn closure ->source_named_context_vacuous M gb gc gn successor ->
 source_named_vacuous M closure target ->source_named_vacuous M successor target ->
 source_named_vacuous M new content ->source_named_vacuous M value content ->source_named_vacuous M selected content ->
 source_named_vacuous M old content ->source_named_vacuous M d content ->source_bounded M content k ->
 source_full_prv M gb gc gn predicate ->source_full_prv M gb gc gn target.
Proof.
 intros BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt HOldNew HValueOld HFresh
  HAssigned HRelative BRelative HMemberValue HMemberResult HResult HMembers
  VCtx BC BE BM BV VT HNewValue HNewX HNewD HSC HFinal HFixed HIncluded HGuard
  HOp HInSelected BInSelected BSC HRawPair HRawProfile HNewPair HProfile VValue HAll VYS VXA SYC SYA SYD HSelectedClosure HSubset HSelectedDef HAccessTail HAccessPoint BAccessPoint HAccessAll
  HSubsetPoint HProfileBody HTarget VSelected VSourceNew VSourceValue BSource BProfileBody
  HSucc HClosure HRepInClosure HOldInClosure HSelectedFresh HSourceBody HSourceEx HRepClosure PRepClosure HDX HDC HRepBody HRepEx VD VTargetD
  VRepNew VRepValue VRepSelected VRepOld BRepBody HEnvClosure PEnvClosure HOldClosure HEnvBody HEnvEx VOld VTargetOld
  VEnvNew VEnvValue VEnvSelected BEnvBody HSucc3 HClosure3 HDef HContentPair HContent
  HCS HCX HCD HSX HSD VC VS VTargetC VTargetS VContentNew VContentValue VContentSelected VContentOld VContentD BContent PDef.
 pose proof(source_local_unpack_content_graph M X definables successor closure succ closureCode accessAll contentPair content
  HSucc HClosure HAccessAll HContentPair HContent)as HContentGraph.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)source_local_unpack_middle)
  (local_unpack_middle_names successor X definables))as(middle&HMiddle).
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 2)source_local_unpack_exists)
  (local_def_names X definables))as(out&HOut).
 destruct(source_local_def_unpack_named_graph M X definables successor closure content middle out HCS HCX HCD HSX HSD
  HContentGraph HMiddle HOut)as(HQC&HQS).
 destruct(sf_relation_total M SFImpl predicate out)as(law&HLaw).
 pose proof(source_full_local_def_unpack M fb fc fn gb gc gn X definables predicate out law k
  HFixed HIncluded BC HDef HOut HLaw PDef)as POut.
 destruct(environment_cons_total M gb gc gn content)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M gb gc gn content ub uc un k HCons)(conj BContent BC))as BU.
 pose proof(source_full_cons_head M gb gc gn content ub uc un k HCons BContent BU)as PContent.
 destruct(source_full_local_unpack_contents M ub uc un succ closureCode accessAll contentPair content HContentPair HContent PContent)
  as(PSucc&PClosure&PAccess).
 assert(HMembers':source_dn_parameter_proofs M count pb pc X ub uc un).
 { intros i v f HI HParam HAtom. exact(source_full_cons_weaken M gb gc gn content ub uc un k f HCons BU(HMembers i v f HI HParam HAtom)). }
 assert(HIncluded':context_included M fb fc fn ub uc un).
 { intros f HF. apply(proj2(context_member_cons M gb gc gn content ub uc un f HCons)). right;exact(HIncluded f HF). }
 pose proof(source_named_context_vacuous_cons M gb gc gn content ub uc un new HCons VCtx VContentNew)as VNew'.
 pose proof(source_named_context_vacuous_cons M gb gc gn content ub uc un value HCons VValue VContentValue)as VValue'.
 pose proof(source_named_context_vacuous_cons M gb gc gn content ub uc un selected HCons VSelected VContentSelected)as VSelected'.
 pose proof(source_named_context_vacuous_cons M gb gc gn content ub uc un old HCons VOld VContentOld)as VOld'.
 pose proof(source_named_context_vacuous_cons M gb gc gn content ub uc un d HCons VD VContentD)as VD'.
 pose proof(source_full_local_def_profile_from_closure_data M count phi rep d X rb rc assignedRep pb pc value vb vc
  environment next old ob oc previous new nb nc target0 extension memberValue memberResult relative assignedPhi result
  fb fc fn ub uc un k sc final guard selected operation inSelected rawPair rawProfile newPair profile allProfile
  closure definables selectedInClosure subset selectedInDef accessTail accessPoint accessAll subsetPoint profileBody target
  successor succ closureCode repInClosure oldInClosure sourceBody sourceEx envClosure envBody envEx repClosure repBody repEx
  BF HRep HOpen HAssignedRep HE HNext HStep HV HO HN HP HT HExt HOldNew HValueOld HFresh
  HAssigned HRelative BRelative HMemberValue HMemberResult HResult HMembers'
  VNew' BU BE BM BV VT HNewValue HNewX HNewD HSC HFinal HFixed HIncluded' HGuard
  HOp HInSelected BInSelected BSC HRawPair HRawProfile HNewPair HProfile VValue' HAll
  VYS VXA SYC SYA SYD HSelectedClosure HSubset HSelectedDef HAccessTail HAccessPoint BAccessPoint HAccessAll
  HSubsetPoint HProfileBody HTarget PAccess VSelected' VSourceNew VSourceValue BSource BProfileBody
  HSucc HClosure HRepInClosure HOldInClosure HSelectedFresh HSourceBody HSourceEx PSucc PClosure
  HRepClosure PRepClosure HDX HDC HRepBody HRepEx VD' VTargetD VRepNew VRepValue VRepSelected VRepOld BRepBody
  HEnvClosure PEnvClosure HOldClosure HEnvBody HEnvEx VOld' VTargetOld VEnvNew VEnvValue VEnvSelected BEnvBody HSucc3 HClosure3)as PTarget.
 destruct(sf_relation_total M SFImpl content target)as(point&HPoint).
 pose proof(source_full_implication_intro M gb gc gn content target point ub uc un HCons HPoint PTarget)as PPoint.
 destruct(sf_relation_total M SFImpl middle target)as(first&HFirst).
 pose proof(source_full_local_named_exists_implication M gb gc gn closure content middle target point first k
  BC BContent VC VTargetC HQC HPoint HFirst PPoint)as PFirst.
 destruct(sf_relation_total M SFImpl out target)as(second&HSecond).
 pose proof(source_full_local_named_exists_implication M gb gc gn successor middle out target first second k
  BC(source_named_quantifier_bound M false closure content middle k BContent HQC)VS VTargetS HQS HFirst HSecond PFirst)as PSecond.
 exact(source_full_modus_ponens M gb gc gn out target second HSecond PSecond POut).
Qed.
Print Assumptions source_full_local_definability_from_data.
