(** Uniform actual inequivalence proofs at arbitrary numerical variable names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift SourceBounded
 SourceDefinabilityBounds SourceDefinabilityLogicalStep SourceNumFDistinctRecipe SourceNumFDistinctCanonical
 SourceNumFDistinctComposition SourceNumFDistinctPrograms SourceUnaryRenamingGraph ThreeNameRenaming
 NumericalRenaming NumericalInstantiation SourcePropositionalTemplates SourcePropositionalRenaming
 SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_numf_distinct_recipe_names M p q canonical x y law:
 source_bounded M p(code_numeral M 1) ->source_bounded M q(code_numeral M 1) ->
 source_numf_distinct_recipe M p q(zeroM M)(code_numeral M 1)canonical ->source_zfr_provable M canonical ->
 source_numf_distinct_recipe M p q x y law ->source_zfr_provable M law.
Proof.
 intros BP BQ(a&b&e&n&i&HA&HB&HE&HN&HI&HC)PC(px&qy&equal&neg&inner&HX&HY&HM&HNeg&HInner&HLaw).
 assert(E:a=p)by(eapply numerical_instantiation_functional;[exact HA|exact(source_unit_instantiation_self M p BP)]). subst a.
 destruct(three_name_renaming_total M x y(zeroM M)(zeroM M))as(rb&rc&HR0&HR1&HR2).
 pose proof(source_unary_instance_renaming_graph M p(zeroM M)p rb rc(code_numeral M 3)(zeroM M)x px
  BP(source_unit_instantiation_self M p BP)HR0 HX)as RP.
 pose proof(source_unary_instance_renaming_graph M q(code_numeral M 1)b rb rc(code_numeral M 3)(zeroM M)y qy BQ HB HR1 HY)as RQ.
 assert(RE:numerical_renaming M e rb rc(code_numeral M 3)(zeroM M)equal).
 { apply(proj2(numerical_renaming_equal M(zeroM M)(code_numeral M 1)e rb rc(code_numeral M 3)(zeroM M)equal HE)). exists x,y. auto. }
 set(env:=fun idx:nat=>match idx with 0=>p|1=>b|_=>e end).
 set(other:=fun idx:nat=>match idx with 0=>px|1=>qy|_=>equal end).
 set(template:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)SPTFalse))).
 assert(GC:code_relation M env(source_prop_expression template)canonical)by(unfold template;nd_graph).
 assert(GL:code_relation M other(source_prop_expression template)law)by(unfold template;nd_graph).
 assert(R:numerical_renaming M canonical rb rc(code_numeral M 3)(zeroM M)law).
 { apply(source_prop_expression_renaming M env other rb rc(code_numeral M 3)(zeroM M)template canonical law);[|exact GC|exact GL].
   intros[|[|idx]];cbn[env other];assumption. }
 apply(proj1(source_zfr_descriptor_provable M law)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor canonical rb rc(code_numeral M 3)(zeroM M)law
  (proj2(source_zfr_descriptor_provable M canonical)PC)R).
Qed.
Theorem source_zfr_numf_distinct_uniform M k l p q x y law:k<>l ->source_numf M k p ->source_numf M l q ->
 source_numf_distinct_recipe M p q x y law ->source_zfr_provable M law.
Proof.
 intros HNE HP HQ HO. destruct(source_numf_distinct_recipe_total M p q(zeroM M)(code_numeral M 1))as(canonical&HC).
 exact(source_zfr_numf_distinct_recipe_names M p q canonical x y law(source_numf_bound M k p HP)(source_numf_bound M l q HQ)HC
  (source_zfr_numf_distinct_canonical M k l p q canonical HNE HP HQ HC)HO).
Qed.
Print Assumptions source_zfr_numf_distinct_recipe_names.
Print Assumptions source_zfr_numf_distinct_uniform.
