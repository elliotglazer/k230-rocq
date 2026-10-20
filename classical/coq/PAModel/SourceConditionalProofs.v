(** Conditional source implications keep their condition as an ordinary
    formula. Their proof predicate is PA-definable and proof-producing. *)
From PAModel Require Import Model NumericalProofs FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceZFRProvability SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors
  SourceWitnessProofComposition SourcePropositionalTemplates SourcePropositionalRebase SourceDescriptorPrograms.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_conditional_fact M condition f :=forall out,
 sf_relation M SFImpl condition f out ->source_zfr_provable M out.
Definition source_conditional_implies M condition a b :=forall point,
 sf_relation M SFImpl a b point ->source_conditional_fact M condition point.
Definition source_conditional_equivalent M condition a b :=
 source_conditional_implies M condition a b /\source_conditional_implies M condition b a.
Definition source_conditional_fact_formula(condition f:term):form :=
 ∀(sf_formula SFImpl condition`[↑] f`[↑] $0 →source_zfr_provable_formula $0).
Definition source_conditional_implies_formula(condition a b:term):form :=
 ∀(sf_formula SFImpl a`[↑] b`[↑] $0 →source_conditional_fact_formula condition`[↑] $0).
Local Opaque holds sf_formula source_zfr_provable_formula.
Theorem source_conditional_fact_formula_correct M rho condition f:
 holds M rho(source_conditional_fact_formula condition f) <->
 source_conditional_fact M(evalM M rho condition)(evalM M rho f).
Proof.
 unfold source_conditional_fact_formula,source_conditional_fact.
 setoid_rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite sf_formula_correct.
 setoid_rewrite source_zfr_provable_formula_correct. unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_conditional_implies_formula_correct M rho condition a b:
 holds M rho(source_conditional_implies_formula condition a b) <->
 source_conditional_implies M(evalM M rho condition)(evalM M rho a)(evalM M rho b).
Proof.
 unfold source_conditional_implies_formula,source_conditional_implies.
 setoid_rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite sf_formula_correct.
 setoid_rewrite source_conditional_fact_formula_correct. unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma source_conditional_reflexive_program C A:
 source_prop_program nil(SPTImpl C(SPTImpl A A)).
Proof. apply SPTII,SPTII,SPTCtx. now left. Qed.

Theorem source_zfr_prop_zero M a(program:source_prop_program nil a)rho k result:
 (forall i,source_bounded M(rho i)k) ->code_relation M rho(source_prop_expression a)result ->source_zfr_provable M result.
Proof.
 intros HB HR. apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_prop_program M ZFRSourceDescriptor nil a program rho k result HB
  (fun p H=>match H with end)HR).
Qed.

Theorem source_conditional_implies_refl M condition a k:
 source_bounded M condition k ->source_bounded M a k ->source_conditional_implies M condition a a.
Proof.
 intros HC HA point HP law HL.
 refine(source_zfr_prop_zero M _ (source_conditional_reflexive_program(SPTSlot 0)(SPTSlot 1))
  (code_parameters condition a a a)k law _ _).
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M (code_parameters condition a a a) SFImpl (SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 1)) condition point law eq_refl
   (source_prop_template_join M (code_parameters condition a a a) SFImpl (SPTSlot 1)(SPTSlot 1) a a point eq_refl eq_refl HP)HL).
Qed.

Theorem source_conditional_fact_of_proof M condition a k:
 source_bounded M condition k ->source_bounded M a k ->source_zfr_provable M a ->source_conditional_fact M condition a.
Proof.
 intros HC HA PA out HO.
 refine(source_zfr_prop_one M (SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 1)) _
  (code_parameters condition a a a)k a out _ eq_refl _ PA).
 - apply SPTII,SPTCtx. right. now left.
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M (code_parameters condition a a a) SFImpl (SPTSlot 0)(SPTSlot 1) condition a out eq_refl eq_refl HO).
Qed.

Print Assumptions source_conditional_fact_formula_correct.
Print Assumptions source_conditional_implies_formula_correct.
Print Assumptions source_conditional_implies_refl.
Print Assumptions source_conditional_fact_of_proof.
