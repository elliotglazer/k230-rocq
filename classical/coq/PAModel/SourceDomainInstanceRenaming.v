(** A unary predicate instance follows any actual numerical renaming. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  NumericalRenamingMaps NumericalRenaming SourceSubstitutionRenaming SourceDomainInstances.
Unset Implicit Arguments.

Theorem source_domain_instance_renaming M domain i f rb rc rn delta g out :
  source_bounded M domain (code_numeral M 1) ->
  numerical_instantiation M domain i f ->numerical_renaming M f rb rc rn delta g ->
  renaming_lookup M rb rc rn delta i out ->numerical_instantiation M domain out g.
Proof.
  intros HD (b&c&HH&HF) HR HL.
  destruct (substitution_singleton_total M out) as (d&e&HH'&_).
  exists d,e. split;[exact HH'|].
  apply (numerical_substitution_then_renaming M domain (code_numeral M 1)
    b c (succM M (zeroM M)) (zeroM M) rb rc rn delta
    d e (succM M (zeroM M)) (zeroM M) f g HD HF HR).
  intros idx u v HI HU HV. rewrite (domain_index_below_one M idx HI) in HU |- *.
  assert (EU:u=i) by (exact (substitution_lookup_functional M b c _ _ _ u i HU HH)). subst u.
  assert (EV:v=out) by (exact (renaming_lookup_functional M rb rc rn delta i v out HV HL)).
  now subst v.
Qed.
Print Assumptions source_domain_instance_renaming.
