(** Literal finite Ext-and-membership witness of the closure law,
    with an arbitrary hygienic output name. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumeralLift SourceEnvInClosureFixed SourceEnvInClosureConstructor
 SourceDefinabilityPrimitives SourceRepresentationClosureRecipe SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterProofs
 SourceFiniteParameterNamedBinder SourceFiniteParameterComposition SourceParameterGraphs SourceNamedQuantifierRules
 OldNamedSyntaxBridge OldFullNDSourceBridge SchemaConstructorBounds SourcePropositionalRebase SourceNumFClosureRecipe.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition eic_extension_body6:sf_form:=($0 ∈' $3)∧isolated_formula(OldZFC.Z_cl.Ext0
 (@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 0)).
Definition eic_extension_sigma i:sf_term:=match i with 0=>$4|1=>$0|_=>$5 end.
Lemma eic_extension_body_shape:eic_extension_body6=($0 ∈' $3)∧source_def_extension021[eic_extension_sigma].
Proof. reflexivity. Qed.
Lemma eic_extension_body_bound:CBound.bounded 6 eic_extension_body6.
Proof.
 unfold eic_extension_body6. apply CBound.bounded_bin.
 - apply CBound.bounded_atom. intros t HT.
   apply Vector.In_cons_iff in HT as[<-|HT];[apply CBound.bounded_var;lia|].
   apply Vector.In_cons_iff in HT as[<-|HT];[apply CBound.bounded_var;lia|]. inversion HT.
 - apply(@isolated_bounded OC.falsity_on 6),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Definition eic_extension_exists_expression:=E_sf SFEx
 (source_parameter_expression(source_parameter_up(source_finite_parameter_names 5))eic_extension_body6)(CEconst 0).
Lemma eic_extension_law_shape:source_env_in_closure_extension_expression=
 E_sf SFImpl(source_parameter_expression(source_finite_parameter_names 5)source_def_successor01)
 (E_sf SFImpl(source_parameter_expression(source_finite_parameter_names 5)representation_closure_condition)
  (E_sf SFImpl(E_sf SFMember(CEvar 3)(CEvar 2))
   (E_sf SFImpl(E_sf SFMember(CEvar 4)(CEvar 0))eic_extension_exists_expression))).
Proof. reflexivity. Qed.
Local Opaque source_def_extension021.
Theorem source_env_in_closure_extension_named M rho z member extension body result:
 (forall i,(i<5)%nat->z<>rho i)->sf_relation M SFMember z(rho 2)member->
 code_relation M(EIC_ext_roles(rho 3)z(rho 4))EIC_ext_expression extension->
 sf_relation M SFAnd member extension body->code_relation M rho eic_extension_exists_expression result->
 source_named_quantifier M false z body result.
Proof.
 intros HF HM HE HB HR.
 apply(source_finite_parameter_named_binder M 5 eic_extension_body6 rho z body result false
  eic_extension_body_bound HF);[|exact HR].
 rewrite eic_extension_body_shape. cbn[source_parameter_expression].
 eapply source_numf_code_join;[| |exact HB].
 - apply(proj2(schema_expression_graph M(finite_binder_environment z rho)SFMember(source_finite_parameter_names 6 0)(source_finite_parameter_names 6 3)z(rho 2)member eq_refl eq_refl)). exact HM.
 - rewrite source_parameter_substitution.
   apply(proj2(source_parameter_graph_ext M 3 source_def_extension021 source_def_extension_bound
    (fun i=>source_finite_parameter_names 6(sf_index(eic_extension_sigma i)))source_three_parameter_names
    (finite_binder_environment z rho)(EIC_ext_roles(rho 3)z(rho 4))
    ltac:(intros[|[|[|i]]]v HI;try lia;reflexivity)extension)). exact HE.
Qed.
Print Assumptions source_env_in_closure_extension_named.
