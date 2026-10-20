(** Literal atomic constructor of the canonical representation recipe.
    Set-relativization adds no guard to a membership or equality atom. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceRepresentationRecipe SourceDefinabilityBounds SourceFiniteCutoffShift NumericalRenamingMaps NumericalRenaming
 SourceSetRelativization SourceSetRelativizationFunctionality SourceDn.
Unset Implicit Arguments.
Theorem source_representation_atomic_shape M count(member:bool)i j phi rep:
 sf_relation M(if member then SFMember else SFEqual)i j phi->source_representation_recipe M count phi rep->
 exists environment first guard atom point,
 source_envf M count environment/\source_cutoff_shift M 1 environment first/\source_cutoff_shift M 1 first guard/\
 sf_relation M(if member then SFMember else SFEqual)(succM M(succM M(succM M i)))(succM M(succM M(succM M j)))atom/\
 code_relation M(representation_point_environment guard atom)(E_representation_point(CEvar 0)(CEvar 1))point/\
 source_dn M count point rep.
Proof.
 intros HAtom(environment&first&guard&matrix&relative&point&HE&H1&H2&HM&HR&HP&HD).
 assert(HMatrix:sf_relation M(if member then SFMember else SFEqual)(succM M(succM M(succM M i)))(succM M(succM M(succM M j)))matrix).
 { destruct member.
   - destruct(proj1(numerical_renaming_member M i j phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix HAtom)HM)as(x&y&HX&HY&HA).
     apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)i x(coding_not_lt_zero M i))in HX.
     apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)j y(coding_not_lt_zero M j))in HY.
     subst x y. rewrite(coding_add_comm M i(code_numeral M 3)),(coding_add_comm M j(code_numeral M 3))in HA.
     change(sf_relation M SFMember(addM M(succM M(succM M(succM M(zeroM M))))i)(addM M(succM M(succM M(succM M(zeroM M))))j)matrix)in HA.
     rewrite!Arithmetic.add_succ,!Arithmetic.add_zero in HA. exact HA.
   - destruct(proj1(numerical_renaming_equal M i j phi(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)matrix HAtom)HM)as(x&y&HX&HY&HA).
     apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)i x(coding_not_lt_zero M i))in HX.
     apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3)j y(coding_not_lt_zero M j))in HY.
     subst x y. rewrite(coding_add_comm M i(code_numeral M 3)),(coding_add_comm M j(code_numeral M 3))in HA.
     change(sf_relation M SFEqual(addM M(succM M(succM M(succM M(zeroM M))))i)(addM M(succM M(succM M(succM M(zeroM M))))j)matrix)in HA.
     rewrite!Arithmetic.add_succ,!Arithmetic.add_zero in HA. exact HA. }
 assert(E:relative=matrix).
 { exact(source_set_relativization_functional M matrix(code_numeral M 2)relative matrix HR
   (source_set_relativization_atom M(code_numeral M 2)(if member then SFMember else SFEqual)_ _ matrix
    ltac:(destruct member;auto)HMatrix)). }
 subst relative. exists environment,first,guard,matrix,point. repeat split;assumption.
Qed.
Print Assumptions source_representation_atomic_shape.
