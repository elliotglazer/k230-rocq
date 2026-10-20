(** Fixed propositional shells and unary domains under actual cutoff maps. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceSubstitutionIdentity SourceDomainInstances
  SourceFiniteCutoffShift SourceQfFunctionality SourcePropositionalTemplates SourcePropositionalSubstitution SourceQuantifierRules.
Unset Implicit Arguments.

Theorem source_cutoff_shift_propositional M depth env other p f g :
  (forall i,source_cutoff_shift M depth(env i)(other i)) ->
  code_relation M env(source_prop_expression p)f ->code_relation M other(source_prop_expression p)g ->
  source_cutoff_shift M depth f g.
Proof.
  intros HH HF HG. destruct(source_cutoff_shift_map_total M depth) as(b&c&n&HM).
  exists b,c,n. split;[exact HM|].
  apply(source_prop_expression_substitution M env other b c n(code_numeral M(S depth))p);[|exact HF|exact HG].
  intro i. destruct(HH i) as(u&v&l&HMap&HSub).
  exact(proj1(numerical_substitution_extensional M(env i)u v l b c n(code_numeral M(S depth))(other i)
    (source_cutoff_shift_maps_equivalent M depth u v l b c n HMap HM))HSub).
Qed.
Theorem source_cutoff_shift_fixes_domain M depth domain :
  source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M(S depth)domain domain.
Proof.
  intro HD. destruct(source_cutoff_shift_map_total M(S depth)) as(b&c&n&HM).
  exists b,c,n. split;[exact HM|].
  apply(numerical_substitution_identity_on_bound M domain b c n(code_numeral M(S(S depth)))(code_numeral M 1)HD).
  intros i HI. rewrite(domain_index_below_one M i HI).
  exact(source_cutoff_shift_map_fixed_lookup M(S depth)b c n HM 0).
Qed.
Theorem source_cutoff_zero_is_shift M f g :source_cutoff_shift M 0 f g ->source_formula_shift M f g.
Proof.
  intros(b&c&n&HMap&HSub). destruct HMap as[-> [-> ->]].
  exact(proj2(numerical_renaming_empty_substitution M f(zeroM M)(zeroM M)(code_numeral M 1)g)HSub).
Qed.
Print Assumptions source_cutoff_shift_propositional.
Print Assumptions source_cutoff_shift_fixes_domain.
Print Assumptions source_cutoff_zero_is_shift.
