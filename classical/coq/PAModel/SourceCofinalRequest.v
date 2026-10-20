(** PA-definable literal request for the uniform cofinal proof family. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SchemaConstructorBounds SourcePropositionalRebase
 SourceFiniteTelescope SourceFiniteParameters SourceFiniteNameParameters SourceCofinalGeometry SourceCofinalCommonPoint SourceCofinalCommonRecipe SourceOrdinalPredicate SourceMembershipBlocks SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition E_cofinal_request:=E_sf SFImpl(CEvar 0)(E_sf SFImpl(CEvar 1)(E_sf SFImpl(CEvar 2)(E_sf SFImpl(CEvar 3)(CEvar 4)))).
Definition source_cofinal_request_env M(member ordinals cover block target:carrier M)i:=
 match i with 0=>member|1=>ordinals|2=>cover|3=>block|_=>target end.
Definition source_cofinal_request_graph M member ordinals cover block target result:=
 code_relation M(source_cofinal_request_env M member ordinals cover block target)E_cofinal_request result.
Theorem source_cofinal_request_telescope M m o c b t r:
 source_cofinal_request_graph M m o c b t r <->source_finite_telescope M(cons m(cons o(cons c(cons b nil))))t r.
Proof.
 unfold source_cofinal_request_graph,E_cofinal_request. split.
 - intro H. destruct(schema_expression_split M _ _ _ _ r H)as(m'&r1&HM&H1&HI0). change(m'=m)in HM. subst m'.
   destruct(schema_expression_split M _ _ _ _ r1 H1)as(o'&r2&HO&H2&HI1). change(o'=o)in HO. subst o'.
   destruct(schema_expression_split M _ _ _ _ r2 H2)as(c'&r3&HC&H3&HI2). change(c'=c)in HC. subst c'.
   destruct(schema_expression_split M _ _ _ _ r3 H3)as(b'&t'&HB&HT&HI3). change(b'=b)in HB. change(t'=t)in HT. subst b' t'.
   exists r1. split;[|exact HI0]. exists r2. split;[|exact HI1].
   exists r3. split;[|exact HI2]. exists t. split;[reflexivity|exact HI3].
 - intros(r1&(r2&(r3&(last&ELast&HI3)&HI2)&HI1)&HI0).
   change(last=t)in ELast. subst last.
   set(rho:=source_cofinal_request_env M m o c b t).
   pose proof(proj2(schema_expression_graph M rho SFImpl(CEvar 3)(CEvar 4)b t r3 eq_refl eq_refl)HI3)as H3.
   pose proof(proj2(schema_expression_graph M rho SFImpl(CEvar 2)(E_sf SFImpl(CEvar 3)(CEvar 4))c r3 r2 eq_refl H3)HI2)as H2.
   pose proof(proj2(schema_expression_graph M rho SFImpl(CEvar 1)(E_sf SFImpl(CEvar 2)(E_sf SFImpl(CEvar 3)(CEvar 4)))o r2 r1 eq_refl H2)HI1)as H1.
   exact(proj2(schema_expression_graph M rho SFImpl(CEvar 0)(E_sf SFImpl(CEvar 1)(E_sf SFImpl(CEvar 2)(E_sf SFImpl(CEvar 3)(CEvar 4))))m r1 r eq_refl H1)HI0).
Qed.
Definition source_cofinal_ordinals_formula(K out:term):form:=code_formula
 (source_parameter_expression(source_finite_parameter_names 1)source_cofinal_ordinals_predicate)(fun _=>K)out.
Definition source_cofinal_cover_formula(K Lb out:term):form:=code_formula
 (source_parameter_expression(source_finite_parameter_names 2)source_cofinal_cover_predicate)(fun (j:nat)=>match j with 0=>K|_=>Lb end)out.
Lemma source_cofinal_ordinals_formula_correct M rho K out:
 holds M rho(source_cofinal_ordinals_formula K out) <->source_cofinal_ordinals M(evalM M rho K)(evalM M rho out).
Proof. unfold source_cofinal_ordinals_formula,source_cofinal_ordinals. rewrite code_formula_correct. reflexivity. Qed.
Lemma source_cofinal_cover_formula_correct M rho K Lb out:
 holds M rho(source_cofinal_cover_formula K Lb out) <->source_cofinal_cover M(evalM M rho K)(evalM M rho Lb)(evalM M rho out).
Proof. unfold source_cofinal_cover_formula,source_cofinal_cover. rewrite code_formula_correct.
 apply(code_relation_ext M _ _ _ _). intros[|i];reflexivity.
Qed.
Definition source_cofinal_request_formula(m o c b t r:term):form:=
 code_formula E_cofinal_request(fun (j:nat)=>match j with 0=>m|1=>o|2=>c|3=>b|_=>t end)r.
Lemma source_cofinal_request_formula_correct M rho m o c b t r:
 holds M rho(source_cofinal_request_formula m o c b t r) <->
 source_cofinal_request_graph M(evalM M rho m)(evalM M rho o)(evalM M rho c)(evalM M rho b)(evalM M rho t)(evalM M rho r).
Proof.
 unfold source_cofinal_request_formula,source_cofinal_request_graph. rewrite code_formula_correct.
 apply(code_relation_ext M _ _ _ _). intros[|[|[|[|i]]]];reflexivity.
Qed.
Definition source_cofinal_proof_at M count:=forall start Ks Lb seed member ordinals cover block target result,
 sf_relation M SFMember seed Ks member ->source_cofinal_ordinals M Ks ordinals ->source_cofinal_cover M Ks Lb cover ->
 source_membership_block M start Lb count block ->source_cofinal_common_recipe M start count Ks target ->
 source_cofinal_request_graph M member ordinals cover block target result ->source_zfr_provable M result.
Definition source_cofinal_proof_formula:form:=∀∀∀∀∀∀∀∀∀∀
 (sf_formula SFMember $6 $8 $5 →source_cofinal_ordinals_formula $8 $4 →source_cofinal_cover_formula $8 $7 $3 →
 source_membership_block_formula $9 $7 $10 $2 →source_cofinal_common_formula $11 $9 $10 $8 $1 →
 source_cofinal_request_formula $5 $4 $3 $2 $1 $0 →source_zfr_provable_formula $0).
Local Opaque holds sf_formula source_cofinal_ordinals_formula source_cofinal_cover_formula source_membership_block_formula source_cofinal_common_formula source_cofinal_request_formula source_zfr_provable_formula.
Lemma source_cofinal_proof_definable M:Definable1 M(source_cofinal_proof_at M).
Proof.
 exists source_cofinal_proof_formula,(source_ordinal_predicate_code M .:fun _=>zeroM M). intro count.
 unfold source_cofinal_proof_formula,source_cofinal_proof_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite sf_formula_correct. setoid_rewrite source_cofinal_ordinals_formula_correct.
 setoid_rewrite source_cofinal_cover_formula_correct. setoid_rewrite source_membership_block_formula_correct.
 setoid_rewrite source_cofinal_common_formula_correct.
 setoid_rewrite source_cofinal_common_point_data_actual.
 setoid_rewrite source_cofinal_request_formula_correct. setoid_rewrite source_zfr_provable_formula_correct.
 reflexivity.
Qed.
Print Assumptions source_cofinal_request_telescope.
Print Assumptions source_cofinal_proof_definable.
