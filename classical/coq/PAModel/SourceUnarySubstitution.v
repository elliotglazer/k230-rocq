(** An actual source substitution transports every instance of a unary
    predicate to the corresponding instance at the substituted name. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceSubstitutionComposition SourceDomainInstances.
Unset Implicit Arguments.

Theorem source_domain_instance_substitution M domain x f rb rc rn base g y :
  source_bounded M domain (code_numeral M 1) ->numerical_instantiation M domain x f ->
  numerical_substitution M f rb rc rn base g ->substitution_lookup M rb rc rn base x y ->
  numerical_instantiation M domain y g.
Proof.
  intros HB (ab&ac&HH&HF) HS HX.
  destruct (substitution_singleton_total M y) as (sb&sc&HHead&_).
  exists sb,sc. split;[exact HHead|].
  apply (numerical_substitution_composition M domain (code_numeral M 1)
    ab ac (code_numeral M 1) (zeroM M) rb rc rn base
    sb sc (code_numeral M 1) (zeroM M) f g HB HF HS).
  intros i j v HI HJ HV. rewrite (domain_index_below_one M i HI) in HJ|-*.
  pose proof (substitution_lookup_functional M ab ac (code_numeral M 1) (zeroM M) _ j x HJ HH) as EJ.
  subst j. pose proof (substitution_lookup_functional M rb rc rn base x v y HV HX) as EV. now subst v.
Qed.

Theorem source_domain_instance_substitution_graph M domain x f rb rc rn base y g :
  source_bounded M domain (code_numeral M 1) ->numerical_instantiation M domain x f ->
  substitution_lookup M rb rc rn base x y ->numerical_instantiation M domain y g ->
  numerical_substitution M f rb rc rn base g.
Proof.
  intros HB HF HX HG. destruct (numerical_substitution_total M f rb rc rn base) as (out&HOut).
  pose proof (source_domain_instance_substitution M domain x f rb rc rn base out y HB HF HOut HX) as HO.
  pose proof (numerical_instantiation_functional M domain y out g HO HG) as E. now subst out.
Qed.

Print Assumptions source_domain_instance_substitution.
Print Assumptions source_domain_instance_substitution_graph.
