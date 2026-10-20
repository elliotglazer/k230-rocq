(** Conditional source congruence under actual quantifier rules. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SourceBounded
 NumericalContexts NumericalSourceFull SourceConditionalProofs SourceConditionalAllIntroduction
 SourceUniversalDistribution SourceExistentialDistribution SourceWitnessProofComposition
 SourceZFRProvability SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors
 SourcePropositionalTemplates SourcePropositionalRebase SourceQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_conditional_trans_program C A B:
 source_prop_program[SPTImpl C A;SPTImpl A B](SPTImpl C B).
Proof.
 apply SPTII. apply(SPTIE _ A B);[apply SPTCtx;cbn;tauto|].
 apply(SPTIE _ C A);apply SPTCtx;cbn;tauto.
Qed.

Theorem source_conditional_implies_quantifier M h condition shifted a b qa qb k:
 sf_unary h ->source_bounded M condition k ->source_formula_shift M condition shifted ->
 source_bounded M a(succM M k) ->source_bounded M b(succM M k) ->
 sf_relation M h a(zeroM M)qa ->sf_relation M h b(zeroM M)qb ->
 source_conditional_implies M shifted a b ->source_conditional_implies M condition qa qb.
Proof.
 intros HH BC HS BA BB HQA HQB IH map HM law HL.
 destruct(sf_relation_total M SFImpl a b)as(point&HP).
 destruct(sf_relation_total M SFAll point(zeroM M))as(qpoint&HQP).
 destruct(sf_relation_total M SFImpl shifted point)as(inner&HInner).
 destruct(sf_relation_total M SFImpl condition qpoint)as(first&HFirst).
 pose proof(proj2(source_bounded_accept_binary M SFImpl a b point(succM M k)
  (or_intror(or_intror eq_refl))HP)(conj BA BB))as BP.
 pose proof(proj2(source_bounded_accept_unary M SFAll point qpoint k(or_introl eq_refl)HQP)BP)as BQP.
 pose proof(proj2(source_bounded_accept_unary M h a qa k HH HQA)BA)as BQA.
 pose proof(proj2(source_bounded_accept_unary M h b qb k HH HQB)BB)as BQB.
 pose proof(proj2(source_bounded_accept_binary M SFImpl qa qb map k
  (or_intror(or_intror eq_refl))HM)(conj BQA BQB))as BM.
 pose proof(source_zfr_conditional_all_introduction M condition shifted point qpoint inner first k
  BC BP HS HQP HInner HFirst(IH point HP inner HInner))as PFirst.
 destruct(sf_relation_total M SFImpl qpoint map)as(dist&HDist).
 assert(PDist:source_zfr_provable M dist).
 { apply(proj1(source_zfr_descriptor_provable M dist)).
   apply(source_descriptor_provable_from_empty M ZFRSourceDescriptor dist).
   destruct HH as[EH|EH];subst h.
   - exact(source_universal_distribution M a b point qa qb qpoint map dist(succM M k)
     BA BB HP HQA HQB HQP HM HDist).
   - exact(source_existential_distribution M a b point qa qb qpoint map dist k
     BA BB HP HQA HQB HQP HM HDist). }
 refine(source_zfr_prop_two M (SPTImpl(SPTSlot 0)(SPTSlot 1))
  (SPTImpl(SPTSlot 1)(SPTSlot 2))(SPTImpl(SPTSlot 0)(SPTSlot 2))
  (source_conditional_trans_program(SPTSlot 0)(SPTSlot 1)(SPTSlot 2))
  (code_parameters condition qpoint map map)k first dist law _ _ _ _ PFirst PDist).
 - intros[|[|[|i]]];cbn[code_parameters];assumption.
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 0)(SPTSlot 1) condition qpoint first eq_refl eq_refl HFirst).
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 1)(SPTSlot 2) qpoint map dist eq_refl eq_refl HDist).
 - exact(source_prop_template_join M _ SFImpl(SPTSlot 0)(SPTSlot 2) condition map law eq_refl eq_refl HL).
Qed.

Print Assumptions source_conditional_implies_quantifier.
