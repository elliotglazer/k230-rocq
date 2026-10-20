(** Actual NumF uniqueness at arbitrary internally coded variable names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceBounded SourceDefinabilityBounds SourceDefinabilityLogicalStep SourceNumFUniqueInduction
 SourceNumFUniqueRecipe SourceNumFUniquePrograms SourceUnaryRenamingGraph ThreeNameRenaming
 NumericalRenaming NumericalInstantiation SourcePropositionalTemplates SourcePropositionalRenaming
 SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_numf_unique_names M n matrix x y px py equal inner law :
 source_numf M n matrix ->numerical_instantiation M matrix x px ->numerical_instantiation M matrix y py ->
 sf_relation M SFEqual x y equal ->sf_relation M SFImpl py equal inner ->sf_relation M SFImpl px inner law ->
 source_zfr_provable M law.
Proof.
 intros HM HX HY HE HI HL.
 destruct(source_numf_unique_recipe_total M matrix)as(canonical&HC).
 pose proof(source_zfr_numf_unique_uniform M n matrix canonical HM HC)as PC.
 destruct(source_numf_unique_recipe_parts M matrix canonical HC)as(ps&ci&HShift&HCI&HCanon).
 pose proof(source_numf_bound M n matrix HM)as BP.
 destruct(three_name_renaming_total M x y(zeroM M)(zeroM M))as(rb&rc&HR0&HR1&HR2).
 pose proof(source_unary_instance_renaming_graph M matrix(zeroM M)matrix rb rc(code_numeral M 3)(zeroM M)x px
 BP(source_unit_instantiation_self M matrix BP)HR0 HX)as RP.
 pose proof(source_unary_instance_renaming_graph M matrix(code_numeral M 1)ps rb rc(code_numeral M 3)(zeroM M)y py
 BP(source_unit_instantiation_shift M matrix ps BP HShift)HR1 HY)as RPS.
 assert(RE:numerical_renaming M(numf_equal01 M)rb rc(code_numeral M 3)(zeroM M)equal).
 { apply(proj2(numerical_renaming_equal M(zeroM M)(code_numeral M 1)(numf_equal01 M)rb rc(code_numeral M 3)(zeroM M)equal(sf_make_numeral M SFEqual 0 1))).
   exists x,y. auto. }
 set(env:=fun idx:nat=>match idx with 0=>matrix|1=>ps|_=>numf_equal01 M end).
 set(other:=fun idx:nat=>match idx with 0=>px|1=>py|_=>equal end).
 assert(GC:code_relation M env(source_prop_expression nu_old)canonical).
 { unfold nu_old. eapply source_prop_template_join;[reflexivity| |exact HCanon].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HCI]. }
 assert(GL:code_relation M other(source_prop_expression nu_old)law).
 { unfold nu_old. eapply source_prop_template_join;[reflexivity| |exact HL].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HI]. }
 assert(RLaw:numerical_renaming M canonical rb rc(code_numeral M 3)(zeroM M)law).
 { apply(source_prop_expression_renaming M env other rb rc(code_numeral M 3)(zeroM M)nu_old canonical law);[|exact GC|exact GL].
   intros[|[|idx]];cbn[env other];assumption. }
 apply(proj1(source_zfr_descriptor_provable M law)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor canonical rb rc(code_numeral M 3)(zeroM M)law
  (proj2(source_zfr_descriptor_provable M canonical)PC)RLaw).
Qed.
Print Assumptions source_zfr_numf_unique_names.
