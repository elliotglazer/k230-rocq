(** Actual primitive equality certificates at arbitrary source names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceRecursionFactsOld SourceRecursionFacts SourceZFRProvability SourcePropositionalRebase
 SetSchemaConstructors SchemaConstructorBounds SourceConditionalProofs SourceConditionalComposition SourceBounded.
Unset Implicit Arguments.
Definition source_equality_atom(equality:bool):=if equality then SFEqual else SFMember.

Ltac source_primitive_graph :=
 repeat first[reflexivity|match goal with
 | H:sf_relation ?M ?h ?a ?b ?out |- code_relation ?M ?rho(E_sf ?h ?A ?B)?out =>
   refine(proj2(schema_expression_graph M rho h A B a b out _ _)H)
 end].
Theorem source_zfr_equal_reflexive M x equal:
 sf_relation M SFEqual x x equal ->source_zfr_provable M equal.
Proof.
 intro HE. apply(source_zfr_recursion_fact_named M RecEqReflexive(code_parameters x x x x)equal).
 change(code_relation M(code_parameters x x x x)(E_sf SFEqual(CEvar 0)(CEvar 0))equal).
 source_primitive_graph.
Qed.
Theorem source_zfr_equal_symmetric M x y old new law:
 sf_relation M SFEqual x y old ->sf_relation M SFEqual y x new ->sf_relation M SFImpl old new law ->source_zfr_provable M law.
Proof.
 intros HO HN HL. apply(source_zfr_recursion_fact_named M RecEqSymmetric(code_parameters x y x x)law).
 change(code_relation M(code_parameters x y x x)
  (E_sf SFImpl(E_sf SFEqual(CEvar 0)(CEvar 1))(E_sf SFEqual(CEvar 1)(CEvar 0)))law).
 source_primitive_graph.
Qed.
Theorem source_zfr_atom_equal_left M equality x y z equal old new point law:
 sf_relation M SFEqual x y equal ->sf_relation M(source_equality_atom equality)x z old ->
 sf_relation M(source_equality_atom equality)y z new ->sf_relation M SFImpl old new point ->
 sf_relation M SFImpl equal point law ->source_zfr_provable M law.
Proof.
 intros HE HO HN HP HL.
 unfold source_equality_atom in HO,HN.
 apply(source_zfr_recursion_fact_named M(if equality then RecEqualLeft else RecMemberLeft)(code_parameters x y z z)law).
 destruct equality.
 - change(code_relation M(code_parameters x y z z)
    (E_sf SFImpl(E_sf SFEqual(CEvar 0)(CEvar 1))(E_sf SFImpl
      (E_sf SFEqual(CEvar 0)(CEvar 2))(E_sf SFEqual(CEvar 1)(CEvar 2))))law).
   source_primitive_graph.
 - change(code_relation M(code_parameters x y z z)
    (E_sf SFImpl(E_sf SFEqual(CEvar 0)(CEvar 1))(E_sf SFImpl
      (E_sf SFMember(CEvar 0)(CEvar 2))(E_sf SFMember(CEvar 1)(CEvar 2))))law).
   source_primitive_graph.
Qed.
Theorem source_zfr_atom_equal_right M equality x y z equal old new point law:
 sf_relation M SFEqual x y equal ->sf_relation M(source_equality_atom equality)z x old ->
 sf_relation M(source_equality_atom equality)z y new ->sf_relation M SFImpl old new point ->
 sf_relation M SFImpl equal point law ->source_zfr_provable M law.
Proof.
 intros HE HO HN HP HL.
 unfold source_equality_atom in HO,HN.
 apply(source_zfr_recursion_fact_named M(if equality then RecEqualRight else RecMemberRight)(code_parameters x y z z)law).
 destruct equality.
 - change(code_relation M(code_parameters x y z z)
    (E_sf SFImpl(E_sf SFEqual(CEvar 0)(CEvar 1))(E_sf SFImpl
      (E_sf SFEqual(CEvar 2)(CEvar 0))(E_sf SFEqual(CEvar 2)(CEvar 1))))law).
   source_primitive_graph.
 - change(code_relation M(code_parameters x y z z)
    (E_sf SFImpl(E_sf SFEqual(CEvar 0)(CEvar 1))(E_sf SFImpl
      (E_sf SFMember(CEvar 2)(CEvar 0))(E_sf SFMember(CEvar 2)(CEvar 1))))law).
   source_primitive_graph.
Qed.
Print Assumptions source_zfr_equal_reflexive.
Print Assumptions source_zfr_equal_symmetric.
Print Assumptions source_zfr_atom_equal_left.
Print Assumptions source_zfr_atom_equal_right.
