(** The arbitrary quantified matrix under the two relevant named scopes.
    The fresh value name is free before scope closing. Neither it nor the
    environment name is identified with a bound de Bruijn slot prematurely. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 SourceNamedScopes SourceNamedScopeBinding SourceSetRelativization SourceSetRelativizationRenaming.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_first_value_matrix M value f named:=numerical_renaming M f value value(code_numeral M 1)(code_numeral M 1)named.
Definition source_quantifier_matrix M head f matrix:=numerical_renaming M f head head(code_numeral M 1)(code_numeral M 3)matrix.
Lemma source_one_role_zero_lookup M head delta:
 renaming_lookup M head head(code_numeral M 1)delta(zeroM M)head.
Proof. left. split;[apply coding_zero_lt_succ|apply beta_singleton]. Qed.
Lemma source_one_role_positive_lookup M head delta i:i<>zeroM M ->
 renaming_lookup M head head(code_numeral M 1)delta i(addM M i delta).
Proof.
 intro HN. right. split;[|reflexivity]. intro H. apply coding_lt_succ_cases in H.
 destruct H as[H|H];[exact(coding_not_lt_zero M i H)|contradiction].
Qed.
Theorem source_quantifier_matrix_scoped M f named matrix value environment k(element_first:bool):
 source_bounded M f k ->~coding_lt M value(succM M k) ->~coding_lt M environment(succM M k) ->
 value<>environment ->source_first_value_matrix M value f named ->
 source_quantifier_matrix M(if element_first then zeroM M else code_numeral M 1)f matrix ->
 named_scope_renaming M(if element_first then[value;environment]else[environment;value])named matrix.
Proof.
 intros BF HV HE HVE HNamed HMatrix.
 set(names:=if element_first then[value;environment]else[environment;value]).
 destruct(named_scope_map_total M names)as(b&c&HMap). exists b,c. split;[exact HMap|].
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  value value(code_numeral M 1)(code_numeral M 1)
  (if element_first then zeroM M else code_numeral M 1)(if element_first then zeroM M else code_numeral M 1)
  (code_numeral M 1)(code_numeral M 3)
  b c(named_scope_bound M names)(code_numeral M(length names))f named matrix BF HId HNamed).
 { unfold names. destruct element_first;exact HMatrix. }
 intros i j l m HI HJ HM HName.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM.
 apply HMap. destruct(@Peano.zero_or_succ(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
 as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l value HName(source_one_role_zero_lookup M value(code_numeral M 1))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(source_one_role_zero_lookup M
    (if element_first then zeroM M else code_numeral M 1)(code_numeral M 3))).
   unfold names. destruct element_first;cbn[named_scope_index].
   + left. auto.
   + right. split;[exact HVE|]. exists(zeroM M). split;[left;auto|reflexivity].
 - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HName(source_one_role_positive_lookup M value(code_numeral M 1)_ HN)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(source_one_role_positive_lookup M
    (if element_first then zeroM M else code_numeral M 1)(code_numeral M 3)_ HN)).
   rewrite<-Arithmetic.succ_as_add.
   assert(HBound:coding_lt M(succM M(succM M q))(succM M k)).
   { exact(proj2(coding_lt_succ_cancel M(succM M q)k)HI). }
   assert(NA:succM M(succM M q)<>value)by(intro E;subst value;contradiction).
   assert(NE:succM M(succM M q)<>environment)by(intro E;subst environment;contradiction).
   replace(addM M(succM M q)(code_numeral M 3))with(succM M(succM M(succM M(succM M q)))).
   2:{ rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
   unfold names. destruct element_first;cbn[named_scope_index].
   + right. split;[exact NA|]. exists(succM M(succM M(succM M q))). split;[|reflexivity].
     right. split;[exact NE|]. exists(succM M(succM M q)). split;reflexivity.
   + right. split;[exact NE|]. exists(succM M(succM M(succM M q))). split;[|reflexivity].
     right. split;[exact NA|]. exists(succM M(succM M q)). split;reflexivity.
Qed.
Theorem source_quantifier_relative_scopes M f named theta child parent value environment k:
 source_bounded M f k ->coding_lt M(zeroM M)k ->
 ~coding_lt M value(succM M k) ->~coding_lt M environment(succM M k) ->value<>environment ->
 source_first_value_matrix M value f named ->source_set_relativization M(code_numeral M 1)named theta ->
 source_quantifier_matrix M(code_numeral M 1)f child ->source_quantifier_matrix M(zeroM M)f parent ->
 exists childtheta parenttheta,
 named_scope_renaming M[environment;value]theta childtheta /\named_scope_renaming M[value;environment]theta parenttheta /\
 source_set_relativization M(code_numeral M 3)child childtheta /\source_set_relativization M(code_numeral M 3)parent parenttheta.
Proof.
 intros BF HK HV HE HVE HNamed HTheta HChild HParent.
 pose proof(source_quantifier_matrix_scoped M f named child value environment k false BF HV HE HVE HNamed HChild)as HC.
 pose proof(source_quantifier_matrix_scoped M f named parent value environment k true BF HV HE HVE HNamed HParent)as HP.
 destruct(named_scope_renaming_total M[environment;value]theta)as(childtheta&HCT).
 destruct(named_scope_renaming_total M[value;environment]theta)as(parenttheta&HPT).
 assert(V1:code_numeral M 1<>value).
 { intro E. subst value. apply HV. exact(proj2(coding_lt_succ_cancel M(zeroM M)k)HK). }
 assert(E1:code_numeral M 1<>environment).
 { intro E. subst environment. apply HE. exact(proj2(coding_lt_succ_cancel M(zeroM M)k)HK). }
 exists childtheta,parenttheta. refine(conj HCT(conj HPT(conj _ _))).
 - destruct HC as(b&c&HM&HC).
   apply(source_set_relativization_renaming M(code_numeral M 1)(code_numeral M 3)named theta b c
    (named_scope_bound M[environment;value])(code_numeral M 2)child childtheta);[|exact HTheta|exact HC|].
   + apply HM. right. split;[exact E1|]. exists(code_numeral M 2). split;[|reflexivity].
     right. split;[exact V1|]. exists(code_numeral M 1). split;reflexivity.
   + exact(named_scope_renaming_at M[environment;value]theta childtheta b c HCT HM).
 - destruct HP as(b&c&HM&HP).
   apply(source_set_relativization_renaming M(code_numeral M 1)(code_numeral M 3)named theta b c
    (named_scope_bound M[value;environment])(code_numeral M 2)parent parenttheta);[|exact HTheta|exact HP|].
   + apply HM. right. split;[exact V1|]. exists(code_numeral M 2). split;[|reflexivity].
     right. split;[exact E1|]. exists(code_numeral M 1). split;reflexivity.
   + exact(named_scope_renaming_at M[value;environment]theta parenttheta b c HPT HM).
Qed.
Print Assumptions source_quantifier_matrix_scoped.
Print Assumptions source_quantifier_relative_scopes.

