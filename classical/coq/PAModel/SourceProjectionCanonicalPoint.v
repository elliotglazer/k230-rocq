(** Match the finite named projection proof with the actual canonical child
    and parent point graphs. All matrix holes remain arbitrary internal codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceFiniteParameterProofs SourceFiniteFamilyBounds
 SourceDefinabilityPrimitives SourceEnvironmentExtensionScopes SourceEnvFScopedHole SourceRepresentativeOneScope
 SourceProjectionChildCalibration SourceProjectionHeadTotal SourceProjectionHeadImage SourceExistentialPointCalibration
 SourceQuantifierMatrixScopes SourceQuantifierHoleAllocation SourceSetRelativization SourceSetRelativizationFunctionality
 SourceRepresentationRecipe SourceNamedHoleEvaluation SourceNamedScopes SourceNamedScopeBinding SourceNamedQuantifierRules
 SourceRepresentativeRenaming NumericalRenaming SourceProjectionProfilePoint SourceProjectionFiniteSyntax SourceZFRProvability.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_projection_canonical_point M f first deep guard child parent childrelative parentrelative pair relative
 namedguard head coverage inAn coveragebody target an childR p a e k q:
 source_bounded M f q ->coding_lt M(zeroM M)q ->
 source_bounded M first k ->source_bounded M namedguard(succM M p) ->
 source_bounded M head k ->source_bounded M coverage k ->
 coding_lt M an k ->coding_lt M childR k ->coding_lt M(code_numeral M 1)k ->coding_lt M(zeroM M)k ->
 ~coding_lt M p k ->~coding_lt M e k ->~coding_lt M a k ->coding_lt M p a ->coding_lt M a e ->
 ~coding_lt M p(succM M q) ->~coding_lt M a(succM M q) ->~coding_lt M e(succM M q) ->
 source_low_parameter_shift M 3 first deep ->source_low_parameter_shift M 1 first guard ->
 source_representative_renaming M p first namedguard ->
 source_quantifier_matrix M(code_numeral M 1)f child ->source_quantifier_matrix M(zeroM M)f parent ->
 source_set_relativization M(code_numeral M 3)child childrelative ->source_set_relativization M(code_numeral M 3)parent parentrelative ->
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))parentrelative pair ->sf_relation M SFEx pair(zeroM M)relative ->
 code_relation M(schema_env3 deep childrelative(succM M(succM M childR)))E_projection_child_head_point head ->
 code_relation M(representation_point_environment guard relative)(E_representation_point(CEvar 0)(CEvar 1))target ->
 sf_relation M SFMember p an inAn ->sf_relation M SFImpl namedguard inAn coveragebody ->source_named_quantifier M true p coveragebody coverage ->
 exists op inner body law,
 code_relation M(projection_five_values an childR(code_numeral M 1)(zeroM M)p)
  (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)op /\
 sf_relation M SFImpl coverage target inner /\sf_relation M SFImpl head inner body /\sf_relation M SFImpl op body law /\source_zfr_provable M law.
Proof.
 intros BF HQ BFirst BN BH BC HAn HChild H1 H0 HP HE HA HPA HAE HPQ HAQ HEQ
  HDeep HGuard HNamed HChildMatrix HParentMatrix HChildRel HParentRel HPair HRelative HHead HTarget HInAn HCoverageBody HCoverage.
 assert(PA:p<>a)by(exact(fun E=>@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)p a HPA E)).
 assert(AE:a<>e)by(exact(fun E=>@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)a e HAE E)).
 assert(PE:p<>e)by(exact(fun E=>@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)p e(coding_lt_trans M p a e HPA HAE)E)).
 assert(A0:zeroM M<>a)by(intro E;subst a;contradiction).
 assert(A1:code_numeral M 1<>a)by(intro E;subst a;contradiction).
 assert(E0:zeroM M<>e)by(intro E;subst e;contradiction).
 assert(P0:zeroM M<>p)by(intro E;subst p;contradiction).
 assert(P1:code_numeral M 1<>p)by(intro E;subst p;contradiction).
 assert(RE:childR<>e)by(intro E;subst e;contradiction).
 assert(RA:childR<>a)by(intro E;subst a;contradiction).
 destruct(source_quantifier_holes_total M f q a e BF HQ HAQ HEQ AE)
  as(namedmatrix&theta&child'&parent'&childrel'&parentrel'&HNM&HTheta&HCM&HPM&HCR&HPR&HChildScope&HParentScope&BNM&BT).
 assert(EC:child'=child)by(eapply numerical_renaming_functional;eassumption). subst child'.
 assert(EP:parent'=parent)by(eapply numerical_renaming_functional;eassumption). subst parent'.
 assert(ECR:childrel'=childrelative)by(eapply source_set_relativization_functional;eassumption). subst childrel'.
 assert(EPR:parentrel'=parentrelative)by(eapply source_set_relativization_functional;eassumption). subst parentrel'.
 destruct(source_quantifier_relative_scopes M f namedmatrix theta child parent a p q BF HQ HAQ HPQ(fun E=>PA(eq_sym E))HNM HTheta HChildMatrix HParentMatrix)
  as(otherchild&otherparent&HOtherChild&HOtherParent&HOtherChildRel&HOtherParentRel).
 assert(EPR:otherparent=parentrelative)by(eapply source_set_relativization_functional;eassumption). subst otherparent.
 destruct(code_relation_total M(source_parameter_expression source_three_parameter_names source_def_extension021)
  (environment_extension_names M p e a))as(extension&HExt).
 destruct(source_finite_names_bound M[p;e;a])as(ke&BNames).
 assert(BExt:source_bounded M extension ke).
 { apply(source_parameter_graph_bounded M 3 source_def_extension021 source_def_extension_bound source_three_parameter_names
  (environment_extension_names M p e a)ke);[|exact HExt].
  intros[|[|[|i]]]v HI HV;try discriminate;try lia.
  - change(v=p)in HV. subst v. exact(BNames p(or_introl eq_refl)).
  - change(v=e)in HV. subst v. exact(BNames e(or_intror(or_introl eq_refl))).
  - change(v=a)in HV. subst v. exact(BNames a(or_intror(or_intror(or_introl eq_refl)))). }
 assert(HFirstScope:named_scope_renaming M[p;e;a]namedguard deep).
 { exact(source_representative_three_scopes M first namedguard deep p e a k BFirst HP HE HA HNamed HDeep). }
 assert(HGuardScope:named_scope_renaming M[p]namedguard guard).
 { exact(source_representative_one_scope M first namedguard guard p k BFirst HP HNamed HGuard). }
 assert(HExtScope:named_scope_renaming M[p;e;a]extension(code_numeral M(sf_encode source_def_extension021))).
 { exact(source_environment_extension_scoped M p e a extension(fun E=>PE(eq_sym E))(fun E=>PA(eq_sym E))AE HExt). }
 assert(BHoles:forall i,exists bound,source_bounded M(projection_child_holes M namedguard extension theta i)bound).
 { intros[|[|i]];[exists(succM M p);exact BN|exists ke;exact BExt|exists(succM M a);exact BT]. }
 destruct(source_hole_named_evaluation_total M(projection_child_names M a e p childR)
  (projection_child_holes M namedguard extension theta)projection_child_template)as(generatedhead&HGeneratedHead).
 pose proof(source_projection_child_head_calibration M a e p childR(projection_child_holes M namedguard extension theta)
  deep childrelative generatedhead BHoles A0 A1 E0 RE RA HFirstScope HExtScope HChildScope HGeneratedHead)as HGeneratedHeadCode.
 assert(EH:generatedhead=head)by(eapply code_relation_functional;eassumption). subst generatedhead.
 assert(BParentHoles:forall i,exists bound,source_bounded M(projection_parent_holes M namedguard theta i)bound).
 { intros[|i];[exists(succM M p);exact BN|exists(succM M a);exact BT]. }
 destruct(source_hole_named_evaluation_total M(existential_point_names M p a)
  (projection_parent_holes M namedguard theta)existential_point_template)as(generatedtarget&HGeneratedTarget).
 pose proof(source_existential_point_calibration M p a(projection_parent_holes M namedguard theta)guard parentrelative pair relative generatedtarget
  BParentHoles P0 P1 A1 PA HGuardScope HOtherParent HPair HRelative HGeneratedTarget)as HGeneratedTargetCode.
 assert(ET:generatedtarget=target)by(eapply code_relation_functional;eassumption). subst generatedtarget.
 exact(source_zfr_projection_head_total M an childR p e a namedguard theta head coverage inAn coveragebody target extension k
  BN BT BH BC HAn HChild H1 H0 HP HE HA HPA HAE HInAn HCoverageBody HCoverage HExt HGeneratedHead HGeneratedTarget).
Qed.
Print Assumptions source_projection_canonical_point.
