(** Actual equality of two values equal to a common third value. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceRecursionFactsOld SourceRecursionFacts SourceZFRProvability SourceEqualityAtomFacts
 SourcePropositionalTemplates SourcePropositionalRebase SourceWitnessProofComposition SetSchemaConstructors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_equal_transitive M x y z xy yz xz point law:
 sf_relation M SFEqual x y xy ->sf_relation M SFEqual y z yz ->sf_relation M SFEqual x z xz ->
 sf_relation M SFImpl yz xz point ->sf_relation M SFImpl xy point law ->source_zfr_provable M law.
Proof.
 intros HXY HYZ HXZ HP HL.
 apply(source_zfr_recursion_fact_named M RecEqTransitive(code_parameters x y z z)law).
 change(code_relation M(code_parameters x y z z)
  (E_sf SFImpl(E_sf SFEqual(CEvar 0)(CEvar 1))(E_sf SFImpl
   (E_sf SFEqual(CEvar 1)(CEvar 2))(E_sf SFEqual(CEvar 0)(CEvar 2))))law).
 source_primitive_graph.
Qed.
Lemma source_equal_common_right_program A B C D:
 source_prop_program[SPTImpl B C;SPTImpl A(SPTImpl C D)](SPTImpl A(SPTImpl B D)).
Proof.
 apply SPTII,SPTII. apply(SPTIE _ C D).
 - apply(SPTIE _ A(SPTImpl C D));apply SPTCtx;cbn;tauto.
 - apply(SPTIE _ B C);apply SPTCtx;cbn;tauto.
Qed.
Theorem source_zfr_equal_common_right M x y z xz yz xy point law k:
 coding_lt M x k ->coding_lt M y k ->coding_lt M z k ->
 sf_relation M SFEqual x z xz ->sf_relation M SFEqual y z yz ->sf_relation M SFEqual x y xy ->
 sf_relation M SFImpl yz xy point ->sf_relation M SFImpl xz point law ->source_zfr_provable M law.
Proof.
 intros BX BY BZ HXZ HYZ HXY HP HL.
 destruct(sf_relation_total M SFEqual z y)as(zy&HZY).
 destruct(sf_relation_total M SFImpl yz zy)as(sym&HSym).
 destruct(sf_relation_total M SFImpl zy xy)as(tail&HTail).
 destruct(sf_relation_total M SFImpl xz tail)as(trans&HTrans).
 pose proof(source_zfr_equal_symmetric M y z yz zy sym HYZ HZY HSym)as PSym.
 pose proof(source_zfr_equal_transitive M x z y xz zy xy tail trans HXZ HZY HXY HTail HTrans)as PTrans.
 set(rho:=code_parameters xz yz zy xy).
 assert(Bounds:forall i,source_bounded M(rho i)k).
 { intros[|[|[|i]]];cbn[rho code_parameters].
   - exact(proj2(source_bounded_accept_atom M SFEqual x z xz k(or_intror eq_refl)HXZ)(conj BX BZ)).
   - exact(proj2(source_bounded_accept_atom M SFEqual y z yz k(or_intror eq_refl)HYZ)(conj BY BZ)).
   - exact(proj2(source_bounded_accept_atom M SFEqual z y zy k(or_intror eq_refl)HZY)(conj BZ BY)).
   - exact(proj2(source_bounded_accept_atom M SFEqual x y xy k(or_intror eq_refl)HXY)(conj BX BY)). }
 refine(source_zfr_prop_two M _ _ _(source_equal_common_right_program(SPTSlot 0)(SPTSlot 1)(SPTSlot 2)(SPTSlot 3))
  rho k sym trans law Bounds _ _ _ PSym PTrans).
 - exact(source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 2)yz zy sym eq_refl eq_refl HSym).
 - exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 2)(SPTSlot 3))xz tail trans eq_refl
   (source_prop_template_join M rho SFImpl(SPTSlot 2)(SPTSlot 3)zy xy tail eq_refl eq_refl HTail)HTrans).
 - exact(source_prop_template_join M rho SFImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 3))xz point law eq_refl
   (source_prop_template_join M rho SFImpl(SPTSlot 1)(SPTSlot 3)yz xy point eq_refl eq_refl HP)HL).
Qed.
Print Assumptions source_zfr_equal_transitive.
Print Assumptions source_zfr_equal_common_right.
