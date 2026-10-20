(** Literal alignment of the implication and carrier coverage points. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeExpressionPlug SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds SourceRepresentationNamedPoint SourceRepresentationPointCompatibility
 SourceRepresentationDifferencePoints SourceImplicationDifferenceProgram SourceImplicationDifferenceUniversal SourcePropositionalTemplates.
Unset Implicit Arguments.
Lemma representation_named_implication_point M rho implication body:
 sf_relation M SFImpl(rho 4)(rho 5)implication->
 (code_relation M rho(E_implication_difference_all implication_difference_conclusion)body<->
 code_relation M(schema_env3(rho 6)implication(succM M(rho 3)))E_representation_named_point body).
Proof.
 intro HC. change(code_relation M rho(code_plug(schema_env3(CEvar 6)(E_sf SFImpl(CEvar 4)(CEvar 5))
    (CEadd(CEvar 3)(CEconst 1)))E_representation_named_point)body<->
    code_relation M(schema_env3(rho 6)implication(succM M(rho 3)))E_representation_named_point body).
 apply representation_named_point_plug;try reflexivity.
 - exact(proj2(schema_expression_graph M rho SFImpl(CEvar 4)(CEvar 5)(rho 4)(rho 5)implication eq_refl eq_refl)HC).
 - exists(rho 3),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add].
Qed.
Lemma representation_implication_carrier_point M rho member inner point:
 sf_relation M SFMember(zeroM M)(succM M(rho 7))member->sf_relation M SFImpl(rho 6)member inner->
 sf_relation M SFAll inner(zeroM M)point->
 code_relation M rho(E_implication_difference_all(SPTImpl(SPTSlot 6)(SPTSlot 7)))point.
Proof.
 intros HM HI HA.
 assert(HName:code_relation M rho(CEadd(CEvar 7)(CEconst 1))(succM M(rho 7))).
 { exists(rho 7),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|apply Arithmetic.succ_as_add]. }
 assert(HMember:code_relation M rho(representation_member_expression(CEvar 7))member).
 { exact(proj2(schema_expression_graph M rho SFMember(CEconst 0)(CEadd(CEvar 7)(CEconst 1))(zeroM M)(succM M(rho 7))member eq_refl HName)HM). }
 assert(HInner:code_relation M rho(E_sf SFImpl(CEvar 6)(representation_member_expression(CEvar 7)))inner).
 { exact(proj2(schema_expression_graph M rho SFImpl(CEvar 6)(representation_member_expression(CEvar 7))(rho 6)member inner eq_refl HMember)HI). }
 exact(proj2(schema_expression_graph M rho SFAll _ (CEconst 0)inner(zeroM M)point HInner eq_refl)HA).
Qed.
Print Assumptions representation_named_implication_point.
Print Assumptions representation_implication_carrier_point.
