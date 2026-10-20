(** PA-definable closure-container statement for the An carrier invariant.
    This file defines the exact target and proof property; it does not
    assume or assert the unfinished arbitrary-count induction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceEnvironmentCarrierRecipe SourceDefinabilityPrimitives SourceRepresentationClosureRecipe
 SourceRepresentationFalsityClosure SourceZFRProvability SchemaConstructorBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.

Definition environment_carrier_closure_expression:=E_sf SFImpl(CEconst(sf_encode source_def_successor01))
 (E_sf SFImpl(CEconst(sf_encode representation_closure_condition))
 (E_sf SFEx(E_sf SFAnd(CEconst(sf_make SFMember 0 3))(CEvar 0))(CEconst 0))).
Definition source_environment_carrier_closure_statement M carrier out:=
 code_relation M(fun _=>carrier)environment_carrier_closure_expression out.
Definition source_environment_carrier_closure_statement_formula(carrier out:term):form:=
 code_formula environment_carrier_closure_expression(fun _=>carrier)out.
Local Opaque holds source_def_successor01 representation_closure_condition code_numeral.
Theorem source_environment_carrier_closure_statement_formula_correct M rho carrier out:
 holds M rho(source_environment_carrier_closure_statement_formula carrier out)<->
 source_environment_carrier_closure_statement M(evalM M rho carrier)(evalM M rho out).
Proof. unfold source_environment_carrier_closure_statement_formula,source_environment_carrier_closure_statement.
 rewrite code_formula_correct. reflexivity. Qed.
Theorem source_environment_carrier_closure_statement_total M carrier:exists out,
 source_environment_carrier_closure_statement M carrier out.
Proof. apply code_relation_total. Qed.
Theorem source_environment_carrier_closure_statement_functional M carrier out other:
 source_environment_carrier_closure_statement M carrier out ->
 source_environment_carrier_closure_statement M carrier other ->out=other.
Proof. apply code_relation_functional. Qed.

Lemma environment_carrier_code_join M rho h A B a b out :
 code_relation M rho A a ->code_relation M rho B b ->sf_relation M h a b out ->
 code_relation M rho(E_sf h A B)out.
Proof. intros HA HB HO. exact(proj2(schema_expression_graph M rho h A B a b out HA HB)HO). Qed.
Theorem source_environment_carrier_closure_statement_join M carrier body ex middle out:
 sf_relation M SFAnd(representation_member_code M)carrier body ->sf_relation M SFEx body(zeroM M)ex ->
 sf_relation M SFImpl(code_numeral M(sf_encode representation_closure_condition))ex middle ->
 sf_relation M SFImpl(code_numeral M(sf_encode source_def_successor01))middle out ->
 source_environment_carrier_closure_statement M carrier out.
Proof.
 intros HB HE HM HO. unfold source_environment_carrier_closure_statement,environment_carrier_closure_expression.
 eapply environment_carrier_code_join;[reflexivity| |exact HO].
 eapply environment_carrier_code_join;[reflexivity| |exact HM].
 eapply environment_carrier_code_join;[|reflexivity|exact HE].
 eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HB].
Qed.

Definition source_environment_carrier_proof_at M count:=forall carrier out,
 source_environment_carrier_recipe M count carrier ->source_environment_carrier_closure_statement M carrier out ->
 source_zfr_provable M out.
Definition source_environment_carrier_proof_formula:form:=∀∀(
 source_environment_carrier_recipe_formula $2 $1 →
 source_environment_carrier_closure_statement_formula $1 $0 →source_zfr_provable_formula $0).
Local Opaque source_environment_carrier_recipe_formula source_environment_carrier_closure_statement_formula source_zfr_provable_formula.
Theorem source_environment_carrier_proof_definable M:Definable1 M(source_environment_carrier_proof_at M).
Proof.
 exists source_environment_carrier_proof_formula,(fun _=>zeroM M). intro count.
 unfold source_environment_carrier_proof_formula,source_environment_carrier_proof_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_environment_carrier_recipe_formula_correct.
 setoid_rewrite source_environment_carrier_closure_statement_formula_correct.
 setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Print Assumptions source_environment_carrier_closure_statement_formula_correct.
Print Assumptions source_environment_carrier_closure_statement_functional.
Print Assumptions source_environment_carrier_proof_definable.
