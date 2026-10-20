(** Actual disjunction elimination from two ordinary implication proofs. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePropositionalTemplates
 SourcePropositionalRebase SchemaConstructorBounds SourceRecursionPrimitiveRelations.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_full_cases M cb cc cn a b target cases left right k:
 source_bounded M a k ->source_bounded M b k ->source_bounded M target k ->context_bounded M cb cc cn k ->
 sf_relation M SFOr a b cases ->sf_relation M SFImpl a target left ->sf_relation M SFImpl b target right ->
 source_full_prv M cb cc cn cases ->source_full_prv M cb cc cn left ->source_full_prv M cb cc cn right ->source_full_prv M cb cc cn target.
Proof.
 intros BA BB BT BC HC HL HR PC PL PR.
 assert(Program:source_prop_program[SPTOr(SPTSlot 0)(SPTSlot 1);SPTImpl(SPTSlot 0)(SPTSlot 2);SPTImpl(SPTSlot 1)(SPTSlot 2)](SPTSlot 2)).
 { apply(SPTDE _ (SPTSlot 0)(SPTSlot 1)).
   - apply SPTCtx;cbn;tauto.
   - apply(SPTIE _ (SPTSlot 0)(SPTSlot 2));apply SPTCtx;cbn;tauto.
   - apply(SPTIE _ (SPTSlot 1)(SPTSlot 2));apply SPTCtx;cbn;tauto. }
 refine(source_prop_program_sound M _ _ Program(source_rec_env3 a b target)k cb cc cn target _ BC _ eq_refl).
 - intros[|[|i]];cbn[source_rec_env3];assumption.
 - intros p[<-|[<-|[<-|[]]]]out HG.
   + pose proof(proj1(schema_expression_graph M(source_rec_env3 a b target)SFOr(CEvar 0)(CEvar 1)a b out eq_refl eq_refl)HG)as HO.
     pose proof(sf_relation_functional M SFOr a b out cases HO HC)as E. now subst out.
   + pose proof(proj1(schema_expression_graph M(source_rec_env3 a b target)SFImpl(CEvar 0)(CEvar 2)a target out eq_refl eq_refl)HG)as HO.
     pose proof(sf_relation_functional M SFImpl a target out left HO HL)as E. now subst out.
   + pose proof(proj1(schema_expression_graph M(source_rec_env3 a b target)SFImpl(CEvar 1)(CEvar 2)b target out eq_refl eq_refl)HG)as HO.
     pose proof(sf_relation_functional M SFImpl b target out right HO HR)as E. now subst out.
Qed.
Print Assumptions source_full_cases.
