(** Literal closure-container representation syntax. The internally varying
    formula occurs only through its genuine representation graph. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes FixedSourceBounds
 SourceBounded SourceBoundedCalibration SourceNumeralLift SourceDefinabilityPrimitives
 SourceRepresentationRecipe SourceRepresentationFalsityClosure SourceClosureNumeralsOld SourceClosureNumeralsFixed
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterIdentityCalibration
 SchemaConstructorBounds OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition representation_closure_condition :sf_form :=isolated_formula
 (OldZFC.Z_cl.Cl(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition representation_raw_closure_body :sf_form :=source_def_empty ∧($0 ∈' $3).
Definition representation_raw_closure_exists :sf_form :=∃representation_raw_closure_body.
Definition representation_successor_expression :=source_parameter_expression(source_finite_parameter_names 3) source_def_successor01.
Definition representation_closure_expression :=source_parameter_expression(source_finite_parameter_names 3) representation_closure_condition.
Definition representation_identity_environment M i :=code_numeral M i.

Lemma representation_closure_empty_shell :source_closure_empty_expression=
 E_sf SFImpl representation_successor_expression(E_sf SFImpl representation_closure_expression
   (source_parameter_expression(source_finite_parameter_names 3) representation_raw_closure_exists)).
Proof. reflexivity. Qed.
Lemma representation_closure_finite_bound :bounded 3 representation_closure_condition.
Proof.
 unfold representation_closure_condition. apply(@isolated_bounded OC.falsity_on 3),
  OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Lemma representation_successor_finite_bound :bounded 3 source_def_successor01.
Proof.
 unfold source_def_successor01. apply(@isolated_bounded OC.falsity_on 3),
  OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Lemma representation_identity_names_graph M i :code_relation M(representation_identity_environment M)
 (source_finite_parameter_names 3 i)(code_numeral M i).
Proof. unfold source_finite_parameter_names. destruct(Nat.ltb i 3);reflexivity. Qed.
Lemma representation_closure_condition_bounded M f :code_relation M(representation_identity_environment M)
 representation_closure_expression f ->source_bounded M f(code_numeral M 3).
Proof.
 apply(source_parameter_graph_bounded M 3 representation_closure_condition representation_closure_finite_bound
  (source_finite_parameter_names 3)(representation_identity_environment M)(code_numeral M 3)).
 intros i x HI HX. rewrite(code_relation_functional M _ _ x(code_numeral M i) HX(representation_identity_names_graph M i)).
 exact(proj2(fixed_source_numeral_lt_iff M i 3) HI).
Qed.
Lemma representation_successor_condition_bounded M f :code_relation M(representation_identity_environment M)
 representation_successor_expression f ->source_bounded M f(code_numeral M 3).
Proof.
 apply(source_parameter_graph_bounded M 3 source_def_successor01 representation_successor_finite_bound
  (source_finite_parameter_names 3)(representation_identity_environment M)(code_numeral M 3)).
 intros i x HI HX. rewrite(code_relation_functional M _ _ x(code_numeral M i) HX(representation_identity_names_graph M i)).
 exact(proj2(fixed_source_numeral_lt_iff M i 3) HI).
Qed.

Definition source_representation_in_closure_recipe M n phi result :=exists rep succ closure targetbody targetex middle,
 source_representation_recipe M n phi rep /\
 code_relation M(representation_identity_environment M) representation_successor_expression succ /\
 code_relation M(representation_identity_environment M) representation_closure_expression closure /\
 sf_relation M SFAnd(representation_member_code M) rep targetbody /\
 sf_relation M SFEx targetbody(zeroM M) targetex /\
 sf_relation M SFImpl closure targetex middle /\sf_relation M SFImpl succ middle result.
Theorem source_representation_in_closure_recipe_total M n phi :exists result,
 source_representation_in_closure_recipe M n phi result.
Proof.
 destruct(source_representation_recipe_total M n phi)as(rep&HR).
 destruct(code_relation_total M representation_successor_expression(representation_identity_environment M))as(succ&HS).
 destruct(code_relation_total M representation_closure_expression(representation_identity_environment M))as(closure&HC).
 destruct(sf_relation_total M SFAnd(representation_member_code M) rep)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(ex&HE).
 destruct(sf_relation_total M SFImpl closure ex)as(middle&HM).
 destruct(sf_relation_total M SFImpl succ middle)as(result&HO).
 exists result,rep,succ,closure,body,ex,middle. exact(conj HR(conj HS(conj HC(conj HB(conj HE(conj HM HO)))))).
Qed.
Theorem source_representation_in_closure_recipe_functional M n phi result other :
 source_representation_in_closure_recipe M n phi result ->
 source_representation_in_closure_recipe M n phi other ->result=other.
Proof.
 intros(r&s&c&b&e&m&HR&HS&HC&HB&HE&HM&HO)(r'&s'&c'&b'&e'&m'&HR'&HS'&HC'&HB'&HE'&HM'&HO').
 assert(r=r')by(eapply source_representation_recipe_functional;eassumption). subst r'.
 assert(s=s')by(eapply code_relation_functional;eassumption). subst s'.
 assert(c=c')by(eapply code_relation_functional;eassumption). subst c'.
 assert(b=b')by(eapply sf_relation_functional;eassumption). subst b'.
 assert(e=e')by(eapply sf_relation_functional;eassumption). subst e'.
 assert(m=m')by(eapply sf_relation_functional;eassumption). subst m'.
 eapply sf_relation_functional;eassumption.
Qed.
Print Assumptions representation_closure_empty_shell.
Print Assumptions representation_closure_condition_bounded.
Print Assumptions representation_successor_condition_bounded.
Print Assumptions source_representation_in_closure_recipe_total.
Print Assumptions source_representation_in_closure_recipe_functional.
