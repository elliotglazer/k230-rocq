(** PA induction closes arbitrarily many guarded assignment variables while
    retaining a condition depending only on representative0 and carrier1. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDn SourceDnBounds SourceDnConditionalStep SourceDescriptorProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_dn_conditional_intro_at M T count :=forall condition body result k point out,
 source_bounded M condition(code_numeral M 2) ->
 source_bounded M body(addM M count(succM M(succM M k))) ->
 source_dn M count body result ->sf_relation M SFImpl condition body point ->
 sf_relation M SFImpl condition result out ->
 source_descriptor_provable M T point ->source_descriptor_provable M T out.
Definition source_dn_conditional_intro_formula T :form :=∀∀∀∀∀∀(
 source_bounded_accept_formula $5(num 2) →source_bounded_accept_formula $4($6 ⊕ σ(σ $2)) →
 source_dn_formula $6 $4 $3 →sf_formula SFImpl $5 $4 $1 →sf_formula SFImpl $5 $3 $0 →
 source_descriptor_provable_formula T $1 →source_descriptor_provable_formula T $0).
Local Opaque holds source_bounded_accept_formula source_dn_formula sf_formula source_descriptor_provable_formula.
Lemma source_dn_conditional_intro_definable M T :Definable1 M(source_dn_conditional_intro_at M T).
Proof.
 exists(source_dn_conditional_intro_formula T),(fun _=>zeroM M). intro count.
 unfold source_dn_conditional_intro_formula,source_dn_conditional_intro_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_dn_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite source_descriptor_provable_formula_correct.
 now repeat setoid_rewrite code_eval_num.
Qed.
Theorem source_descriptor_dn_conditional_intro M T count :source_dn_conditional_intro_at M T count.
Proof.
 revert count. apply(definable_induction M(source_dn_conditional_intro_at M T)
   (source_dn_conditional_intro_definable M T)).
 - intros condition body result k point out HC HB HD HP HO PP.
   apply source_dn_zero in HD. subst result.
   rewrite(sf_relation_functional M SFImpl condition body out point HO HP). exact PP.
 - intros count IH condition body result k point out HC HB HD HP HO PP.
   apply source_dn_succ in HD. destruct HD as(previous&HD&HS).
   assert(E:addM M(succM M count)(succM M(succM M k))=
     addM M count(succM M(succM M(succM M k)))).
   { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count(succM M(succM M(succM M k)))),
      Arithmetic.add_succ,(Arithmetic.add_comm M(succM M(succM M k)) count). reflexivity. }
   rewrite E in HB.
   destruct(sf_relation_total M SFImpl condition previous)as(previousPoint&HPreviousPoint).
   pose proof(IH condition body previous(succM M k) point previousPoint HC HB HD HP HPreviousPoint PP)as PPrevious.
   exact(source_descriptor_dn_successor_conditional_intro M T condition previous result previousPoint out k HC
    (source_dn_bounded M count body previous(succM M k) HD HB) HS HPreviousPoint HO PPrevious).
Qed.
Print Assumptions source_dn_conditional_intro_definable.
Print Assumptions source_descriptor_dn_conditional_intro.
