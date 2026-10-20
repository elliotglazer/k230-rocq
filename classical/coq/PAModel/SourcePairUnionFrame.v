(** Literal pair/union conditions and their padding through internal Dn. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs
 SourceParameterRenamingTransport SourceRepresentationPadding SourceRepresentationConjunctionFrame
 SourceRepresentationDifferencePadding SourceRepresentationDifferencePoints SourceRepresentationDifferenceProgram
 SourcePairUnionProfileFixed SourcePairUnionProgram SourceZFRProvability.
From OldZFC Require Z_base Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia Arith.PeanoNat.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition pair_union_pair_source:sf_form:=isolated_formula(OldZFC.Z_base.Pair0
 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition pair_union_union_source:sf_form:=isolated_formula(OldZFC.Z_base.Union0
 (@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)).
Definition pair_union_profile_source:sf_form:=∀($0 ∈' $4 ↔($0 ∈' $1 ∨$0 ∈' $2)).
Definition E_pair_union_pair:=source_parameter_expression(source_finite_parameter_names 4)pair_union_pair_source.
Definition E_pair_union_union:=source_parameter_expression(source_finite_parameter_names 4)pair_union_union_source.
Definition E_pair_union_profile:=source_parameter_expression(source_finite_parameter_names 4)pair_union_profile_source.
Lemma pair_union_literal_law_shape:source_pair_union_profile_law=
 (pair_union_pair_source →pair_union_union_source →pair_union_profile_source).
Proof. reflexivity. Qed.
Lemma pair_union_profile_expression_shape:E_pair_union_profile=E_double_difference_all pair_union_profile_template.
Proof. reflexivity. Qed.
Lemma pair_union_pair_bound:bounded 4 pair_union_pair_source.
Proof.
 apply(@isolated_bounded OC.falsity_on 4(OldZFC.Z_base.Pair0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Lemma pair_union_union_bound:bounded 4 pair_union_union_source.
Proof.
 apply(@isolated_bounded OC.falsity_on 4(OldZFC.Z_base.Union0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3))).
 apply OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_zfr_pair_union_profile_shell M rho pair union profile inner law:
 code_relation M rho E_pair_union_pair pair ->code_relation M rho E_pair_union_union union ->
 code_relation M rho(E_double_difference_all pair_union_profile_template)profile ->
 sf_relation M SFImpl union profile inner ->sf_relation M SFImpl pair inner law ->source_zfr_provable M law.
Proof.
 intros HP HU HProfile HI HL. apply(source_zfr_pair_union_profile_named M rho law).
 unfold source_pair_union_profile_graph. rewrite pair_union_literal_law_shape.
 change(code_relation M rho(E_sf SFImpl E_pair_union_pair(E_sf SFImpl E_pair_union_union E_pair_union_profile))law).
 rewrite pair_union_profile_expression_shape.
 exact(proj2(schema_expression_graph M rho SFImpl _ _ pair inner law HP
  (proj2(schema_expression_graph M rho SFImpl _ _ union profile inner HU HProfile)HI))HL).
Qed.
Theorem pair_union_parameter_bound M phi rho k out:bounded 4 phi ->
 (forall i,(i<4)%nat ->coding_lt M(rho i)k) ->
 code_relation M rho(source_parameter_expression(source_finite_parameter_names 4)phi)out ->source_bounded M out k.
Proof.
 intros HB HNames HOut. apply(source_parameter_graph_bounded M 4 phi HB(source_finite_parameter_names 4)rho k);[|exact HOut].
 intros i x HI HX. unfold source_finite_parameter_names in HX.
 assert(E:Nat.ltb i 4=true)by(now apply Nat.ltb_lt). rewrite E in HX.
 change(x=rho i)in HX. subst x. now apply HNames.
Qed.
Theorem source_pair_union_condition_padding M count rho other pair union condition pair' union' padded:
 (forall i,(i<4)%nat ->representation_padding_lookup M count(rho i)(other i)) ->
 code_relation M rho E_pair_union_pair pair ->code_relation M rho E_pair_union_union union ->
 code_relation M other E_pair_union_pair pair' ->code_relation M other E_pair_union_union union' ->
 sf_relation M SFAnd pair union condition ->sf_relation M SFAnd pair' union' padded ->
 source_representation_padding M count condition padded.
Proof.
 intros HNames HP HU HP' HU' HC HC'.
 assert(HMap:forall phi out otherOut,bounded 4 phi ->
  code_relation M rho(source_parameter_expression(source_finite_parameter_names 4)phi)out ->
  code_relation M other(source_parameter_expression(source_finite_parameter_names 4)phi)otherOut ->
  source_representation_padding M count out otherOut).
 { intros phi out otherOut HB HO HO'.
   apply(source_parameter_renaming_transport M 4 phi HB(source_finite_parameter_names 4)(source_finite_parameter_names 4)
    rho other(code_numeral M 6)(code_numeral M 2)(code_numeral M 2)count out otherOut);[|exact HO|exact HO'].
   intros i x y HI HX HY. unfold source_finite_parameter_names in HX,HY.
   assert(E:Nat.ltb i 4=true)by(now apply Nat.ltb_lt). rewrite E in HX,HY.
   change(x=rho i)in HX. change(y=other i)in HY. subst x y. now apply HNames. }
 exact(source_representation_difference_condition_padding M count pair union pair' union' condition padded
  (HMap pair_union_pair_source pair pair' pair_union_pair_bound HP HP')
  (HMap pair_union_union_source union union' pair_union_union_bound HU HU')HC HC').
Qed.
Print Assumptions pair_union_profile_expression_shape.
Print Assumptions source_zfr_pair_union_profile_shell.
Print Assumptions pair_union_parameter_bound.
Print Assumptions source_pair_union_condition_padding.
