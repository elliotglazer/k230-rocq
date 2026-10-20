(** Exact decomposition of the canonical existential representation recipe.
    Its arbitrary internal matrix is retained under the actual lifted map and
    moving carrier; only the finite outer constructor is inspected. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceRepresentationRecipe SourceQuantifierMatrixScopes NumericalRenamingMaps NumericalRenaming
 SourceSetRelativization SourceSetRelativizationFunctionality SourceSetRelativizationRules SourceShiftSpecialization
 SourceDefinabilityIteration SourceDefinabilityBounds SourceFiniteCutoffShift SourceDn.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Lemma source_empty_three_lift_equivalent M b c n:
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)b c n ->
 renaming_equivalent M b c n(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3).
Proof.
 intros HL i v. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - pose proof(proj2(renaming_lift_head M _ _ _ _ b c n(zeroM M)HL)eq_refl)as HOld.
   pose proof(source_one_role_zero_lookup M(zeroM M)(code_numeral M 3))as HNew.
   split;intro H.
   + rewrite(renaming_lookup_functional M _ _ _ _ _ v _ H HOld). exact HNew.
   + rewrite(renaming_lookup_functional M _ _ _ _ _ v _ H HNew). exact HOld.
 - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   pose proof(source_one_role_positive_lookup M(zeroM M)(code_numeral M 3)(succM M q)HN)as HNew.
   assert(HOld:renaming_lookup M b c n(code_numeral M 3)(succM M q)(addM M(succM M q)(code_numeral M 3))).
   { rewrite Arithmetic.add_succ. apply(proj2(renaming_lift_tail M _ _ _ _ b c n q(addM M q(code_numeral M 3))HL)).
     right. exact(conj(coding_not_lt_zero M q)eq_refl). }
   split;intro H.
   + rewrite(renaming_lookup_functional M _ _ _ _ _ v _ H HOld). exact HNew.
   + rewrite(renaming_lookup_functional M _ _ _ _ _ v _ H HNew). exact HOld.
Qed.
Theorem source_representation_existential_recipe M count f existential result:
 sf_relation M SFEx f(zeroM M)existential ->source_representation_recipe M count existential result ->
 exists environment first shifted parent parentrelative pair relative point,
 source_envf M count environment /\source_cutoff_shift M 1 environment first /\source_cutoff_shift M 1 first shifted /\
 source_quantifier_matrix M(zeroM M)f parent /\source_set_relativization M(code_numeral M 3)parent parentrelative /\
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))parentrelative pair /\sf_relation M SFEx pair(zeroM M)relative /\
 code_relation M(representation_point_environment shifted relative)(E_representation_point(CEvar 0)(CEvar 1))point /\
 source_dn M count point result.
Proof.
 intros HEx(environment&first&shifted&matrix&relative&point&HE&H1&H2&HM&HR&HP&HD).
 destruct(proj1(numerical_renaming_quantifier M false f existential(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix HEx)HM)
  as(b&c&n&parent&HL&HParent&HMatrix).
 pose proof(proj1(numerical_renaming_extensional M f b c n(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)parent
  (source_empty_three_lift_equivalent M b c n HL))HParent)as HParentMap.
 destruct(source_set_relativization_quantifier_inv M(code_numeral M 2)false parent matrix relative HMatrix HR)
  as(parentrelative&HParentRelative&guard&pair&HGuard&HPair&HRelative).
 assert(EGuard:guard=code_numeral M(sf_make SFMember 0 3)).
 { exact(sf_relation_functional M SFMember(zeroM M)(code_numeral M 3)guard _ HGuard(sf_make_numeral M SFMember 0 3)). }
 subst guard.
 exists environment,first,shifted,parent,parentrelative,pair,relative,point.
 exact(conj HE(conj H1(conj H2(conj HParentMap(conj HParentRelative(conj HPair(conj HRelative(conj HP HD)))))))).
Qed.
Print Assumptions source_empty_three_lift_equivalent.
Print Assumptions source_representation_existential_recipe.
