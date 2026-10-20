(** Actual atomic-operation theorem in independently named literal source
    constructors. Every finite subformula is calibrated to the pinned Op6/7. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 OldNamedSyntaxBridge SourceFiniteParameters SourceFiniteNameParameters SourcePropositionalRebase
 SourceEnvFLookupProfile SourceEnvFLookupProfileCalibration SourceAtomicOperationSyntax SourceAtomLookupOld SourceAtomOperationOld SourceAtomOperationFixed
 SourceIffGraphs SourceZFRProvability.
Unset Implicit Arguments.
Definition source_atom_roles{A}(e xi xj a b carrier representative:A)i:=match i with
 |0=>e|1=>xi|2=>xj|3=>a|4=>b|5=>carrier|_=>representative end.
Definition E_atomic_operation_law names(member:bool):=E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_cl.Op(if member then 6 else 7)
  (@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 6))))
  (E_sf SFImpl(E_sf SFMember(names 0)(names 5))
   (E_sf SFImpl(source_parameter_expression names(isolated_formula(old_atom_app_profile(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 3))))
    (E_sf SFImpl(source_parameter_expression names(isolated_formula(old_atom_app_profile(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 4))))
     (E_sf_iff(E_sf SFMember(names 0)(names 6))(E_sf(if member then SFMember else SFEqual)(names 3)(names 4)))))).
Lemma source_atom_operation_expression_literal member:source_atom_operation_expression member=
 E_atomic_operation_law(source_finite_parameter_names 7)member.
Proof. destruct member;reflexivity. Qed.
Theorem source_zfr_atomic_operation_shell M(member:bool)e xi xj a b carrier representative op memCarrier left right atom memRepresentative equiv:
 source_atomic_operation M member carrier xi xj representative op->
 sf_relation M SFMember e carrier memCarrier->source_env_profile M e xi a left->source_env_profile M e xj b right->
 sf_relation M(if member then SFMember else SFEqual)a b atom->sf_relation M SFMember e representative memRepresentative->
 source_iff_graph M memRepresentative atom equiv->
 exists last third second law,
 sf_relation M SFImpl right equiv last/\sf_relation M SFImpl left last third/\
 sf_relation M SFImpl memCarrier third second/\sf_relation M SFImpl op second law/\source_zfr_provable M law.
Proof.
 intros HOp HCarrier HLeft HRight HAtom HRepresentative HIff.
 set(rho:=source_atom_roles e xi xj a b carrier representative).
 set(names:=source_finite_parameter_names 7).
 destruct(code_relation_total M(source_parameter_expression names(isolated_formula(OldZFC.Z_cl.Op(if member then 6 else 7)
  (@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 6))))rho)as(op'&GOp).
 pose proof(source_parameter_atomic_operation_instance M member names rho 5 1 2 6 carrier xi xj representative op'
  eq_refl eq_refl eq_refl eq_refl GOp)as HOp'.
 assert(E:op'=op)by(eapply code_relation_functional;[exact HOp'|exact HOp]). subst op'.
 destruct(code_relation_total M(source_parameter_expression names(isolated_formula(old_atom_app_profile
  (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 3))))rho)as(left'&GL).
 pose proof(source_parameter_env_profile_instance M names rho 0 1 3 e xi a left' eq_refl eq_refl eq_refl GL)as HL.
 assert(E:left'=left)by(eapply source_env_profile_functional;eassumption). subst left'.
 destruct(code_relation_total M(source_parameter_expression names(isolated_formula(old_atom_app_profile
  (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 4))))rho)as(right'&GR).
 pose proof(source_parameter_env_profile_instance M names rho 0 2 4 e xj b right' eq_refl eq_refl eq_refl GR)as HR.
 assert(E:right'=right)by(eapply source_env_profile_functional;eassumption). subst right'.
 assert(GCarrier:code_relation M rho(E_sf SFMember(names 0)(names 5))memCarrier).
 { exact(proj2(schema_expression_graph M rho SFMember(names 0)(names 5)e carrier memCarrier eq_refl eq_refl)HCarrier). }
 assert(GRepresentative:code_relation M rho(E_sf SFMember(names 0)(names 6))memRepresentative).
 { exact(proj2(schema_expression_graph M rho SFMember(names 0)(names 6)e representative memRepresentative eq_refl eq_refl)HRepresentative). }
 assert(GAtom:code_relation M rho(E_sf(if member then SFMember else SFEqual)(names 3)(names 4))atom).
 { exact(proj2(schema_expression_graph M rho(if member then SFMember else SFEqual)(names 3)(names 4)a b atom eq_refl eq_refl)HAtom). }
 assert(GIff:code_relation M rho(E_sf_iff(E_sf SFMember(names 0)(names 6))(E_sf(if member then SFMember else SFEqual)(names 3)(names 4)))equiv).
 { destruct(source_iff_parts M memRepresentative atom equiv HIff)as(lr&rl&HLR&HRL&HEq).
   assert(GLR:code_relation M rho(E_sf SFImpl(E_sf SFMember(names 0)(names 6))(E_sf(if member then SFMember else SFEqual)(names 3)(names 4)))lr).
   { exact(proj2(schema_expression_graph M rho SFImpl _ _ memRepresentative atom lr GRepresentative GAtom)HLR). }
   assert(GRL:code_relation M rho(E_sf SFImpl(E_sf(if member then SFMember else SFEqual)(names 3)(names 4))(E_sf SFMember(names 0)(names 6)))rl).
   { exact(proj2(schema_expression_graph M rho SFImpl _ _ atom memRepresentative rl GAtom GRepresentative)HRL). }
   exact(proj2(schema_expression_graph M rho SFAnd _ _ lr rl equiv GLR GRL)HEq). }
 destruct(sf_relation_total M SFImpl right equiv)as(last&HLast).
 destruct(sf_relation_total M SFImpl left last)as(third&HThird).
 destruct(sf_relation_total M SFImpl memCarrier third)as(second&HSecond).
 destruct(sf_relation_total M SFImpl op second)as(law&HLaw).
 exists last,third,second,law. refine(conj HLast(conj HThird(conj HSecond(conj HLaw _)))).
 apply(source_zfr_atom_operation M member rho law).
 rewrite source_atom_operation_expression_literal. change(code_relation M rho(E_atomic_operation_law names member)law).
 unfold E_atomic_operation_law.
 exact(proj2(schema_expression_graph M rho SFImpl _ _ op second law GOp
  (proj2(schema_expression_graph M rho SFImpl _ _ memCarrier third second GCarrier
   (proj2(schema_expression_graph M rho SFImpl _ _ left last third GL
    (proj2(schema_expression_graph M rho SFImpl _ _ right equiv last GR GIff)HLast))HThird))HSecond))HLaw).
Qed.
Print Assumptions source_zfr_atomic_operation_shell.
