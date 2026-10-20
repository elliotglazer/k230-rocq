(** Close one fresh representative name in an arbitrary internal formula.
    Only representative0 is captured; its parameter tail moves by one. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 SourceRepresentativeRenaming SourceEnvFScopedHole SourceNamedScopes SourceNamedScopeBinding.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_representative_one_scope M f renamed shifted p k:
 source_bounded M f k ->~coding_lt M p k ->
 source_representative_renaming M p f renamed ->source_low_parameter_shift M 1 f shifted ->
 named_scope_renaming M[p]renamed shifted.
Proof.
 intros BF HP HR HShift.
 destruct(named_scope_map_total M[p])as(b&c&HMap). exists b,c. split;[exact HMap|].
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)p p(code_numeral M 1)(zeroM M)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1)
  b c(named_scope_bound M[p])(code_numeral M 1)f renamed shifted BF HId HR HShift).
 intros i j l m HI HJ HM HName.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM.
 apply HMap.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l p HName(representative_lookup_zero M p)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(low_parameter_lookup_zero M 1)). left. auto.
 - assert(HNon:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HName(representative_lookup_nonzero M p(succM M q)HNon)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(low_parameter_lookup_nonzero M 1(succM M q)HNon)).
   right. split;[intro E;subst p;contradiction|]. exists(succM M q). split;[reflexivity|].
   cbn[named_scope_succ]. rewrite<-Arithmetic.succ_as_add. reflexivity.
Qed.
Print Assumptions source_representative_one_scope.
