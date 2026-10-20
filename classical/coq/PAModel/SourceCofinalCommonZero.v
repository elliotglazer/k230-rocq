(** Full current numerical zero-count proof, with only literal ordinary
    seed-in-K and Ordinals(K) antecedents. No source proof premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SchemaConstructorBounds NumericalInstantiation
 SourceCofinalGeometry SourceCofinalCommonRecipe SourceCofinalCommonBase SourceCofinalCommonBaseOld
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourcePropositionalRebase SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_zfr_cofinal_common_zero M K seed start member ordinals target tail law :
 sf_relation M SFMember seed K member ->source_cofinal_ordinals M K ordinals ->
 source_cofinal_common_recipe M start(zeroM M)K target ->
 sf_relation M SFImpl ordinals target tail ->sf_relation M SFImpl member tail law ->
 source_zfr_provable M law.
Proof.
 intros HM HOrd HT HTail HLaw.
 set(rho:=fun i:nat=>match i with 0=>K|_=>seed end).
 destruct(code_relation_total M source_cofinal_common_seed_expression rho)as(proof&HP).
 pose proof(source_zfr_cofinal_common_seed M rho proof HP)as PP.
 change(code_relation M rho(E_sf SFImpl(E_sf SFMember(CEvar 1)(CEvar 0))
 (E_sf SFImpl(source_parameter_expression(source_finite_parameter_names 2)source_cofinal_ordinals_predicate)
 source_cofinal_common_empty_expression))proof)in HP.
 destruct(schema_expression_split M rho _ _ _ proof HP)as(member'&tail'&HMem&HTail'&HProof).
 destruct(schema_expression_split M rho _ _ _ tail' HTail')as(ordinals'&target'&HOrd'&HTarget'&HBody).
 assert(HM':sf_relation M SFMember seed K member').
 { exact(proj1(schema_expression_graph M rho SFMember(CEvar 1)(CEvar 0)seed K member' eq_refl eq_refl)HMem). }
 pose proof(sf_relation_functional M SFMember seed K member member' HM HM')as E. subst member'.
 assert(HOrdSame:code_relation M rho(source_parameter_expression(source_finite_parameter_names 2)source_cofinal_ordinals_predicate)ordinals).
 { apply(proj1(source_parameter_graph_ext M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
   (source_finite_parameter_names 1)(source_finite_parameter_names 2)(fun _=>K)rho
   ltac:(intros[|i]x HI;try lia;reflexivity)ordinals)). exact HOrd. }
 pose proof(code_relation_functional M _ rho ordinals ordinals' HOrdSame HOrd')as E. subst ordinals'.
 pose proof(source_cofinal_common_empty_parameter_graph M rho target' start HTarget')as HT'.
 change(source_cofinal_common_recipe M start(zeroM M)K target')in HT'.
 pose proof(source_cofinal_common_recipe_functional M start(zeroM M)K target target' HT HT')as E. subst target'.
 pose proof(sf_relation_functional M SFImpl ordinals target tail tail' HTail HBody)as E. subst tail'.
 pose proof(sf_relation_functional M SFImpl member tail law proof HLaw HProof)as E. now subst proof.
Qed.
Print Assumptions source_zfr_cofinal_common_zero.
