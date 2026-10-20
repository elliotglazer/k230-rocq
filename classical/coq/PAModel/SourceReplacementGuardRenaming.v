(** Actual RepA/RepB renaming of the guarded Replacement matrix. The domain
    may be any bounded-one internally coded formula. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceSubstitutionRenaming NumericalRenamingMaps NumericalRenaming
  SourceDomainInstances SourceQuantifierRules SchemaRenamingDescriptors
  SourceRelativeSchemaInputs.
Unset Implicit Arguments.

Theorem source_domain_instance_renaming M domain i f b c n delta g j :
  source_bounded M domain (code_numeral M 1) ->
  numerical_instantiation M domain i f -> numerical_renaming M f b c n delta g ->
  renaming_lookup M b c n delta i j -> numerical_instantiation M domain j g.
Proof.
  intros HD [ab [ac [HH HF]]] HR HJ.
  destruct (substitution_singleton_total M j) as [cb [cc [HH' _]]].
  exists cb,cc. split;[exact HH'|].
  apply (numerical_substitution_then_renaming M domain (code_numeral M 1)
    ab ac (succM M (zeroM M)) (zeroM M) b c n delta
    cb cc (succM M (zeroM M)) (zeroM M) f g HD HF HR).
  intros x u v HX HU HV. rewrite (domain_index_below_one M x HX) in HU.
  assert (EU:u=i) by (eapply substitution_lookup_functional;[exact HU|exact HH]).
  subst u.
  assert (EV:v=j) by (eapply renaming_lookup_functional;[exact HV|exact HJ]).
  subst v. rewrite (domain_index_below_one M x HX). exact HH'.
Qed.

Theorem source_guarded_matrix_schema_renaming M s domain rphi matrix body out first second :
  source_bounded M domain (code_numeral M 1) ->
  relative_replacement_matrix M domain rphi matrix ->
  schema_renaming M s matrix out -> schema_renaming M s rphi body ->
  numerical_instantiation M domain (code_numeral M (schema_first s)) first ->
  numerical_instantiation M domain (code_numeral M (schema_second s)) second ->
  exists guards,sf_relation M SFAnd first second guards /\ sf_relation M SFAnd guards body out.
Proof.
  intros HD [d1 [guards [H1 [HG HM]]]] HOut HBody HFirst HSecond.
  apply (proj1 (numerical_renaming_binary M SFAnd guards rphi matrix
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) out
    (or_introl eq_refl) HM)) in HOut.
  destruct HOut as [rg [rb [HRG [HRB HOut]]]].
  pose proof (numerical_renaming_functional M rphi
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) rb body HRB HBody) as E.
  subst rb.
  apply (proj1 (numerical_renaming_binary M SFAnd domain d1 guards
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) rg
    (or_introl eq_refl) HG)) in HRG.
  destruct HRG as [rd0 [rd1 [HR0 [HR1 HRG]]]].
  pose proof (source_domain_instance_renaming M domain (zeroM M) domain
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) rd0
    (code_numeral M (schema_first s)) HD (source_domain_instance_zero M domain HD) HR0
    (proj2 (schema_lookup_first M s _) eq_refl)) as HI0.
  pose proof (numerical_instantiation_functional M domain
    (code_numeral M (schema_first s)) rd0 first HI0 HFirst) as E0.
  pose proof (source_domain_instance_renaming M domain (code_numeral M 1) d1
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) rd1
    (code_numeral M (schema_second s)) HD H1 HR1
    (proj2 (schema_lookup_second M s _) eq_refl)) as HI1.
  pose proof (numerical_instantiation_functional M domain
    (code_numeral M (schema_second s)) rd1 second HI1 HSecond) as E1.
  subst rd0 rd1. exists rg. auto.
Qed.

Theorem source_replacement_guarded_pair_shapes M domain d1 d2 rphi matrix ra rb ma mb :
  source_bounded M domain (code_numeral M 1) ->
  source_formula_shift M domain d1 -> source_formula_shift M d1 d2 ->
  relative_replacement_matrix M domain rphi matrix ->
  schema_renaming M RepA matrix ma -> schema_renaming M RepB matrix mb ->
  schema_renaming M RepA rphi ra -> schema_renaming M RepB rphi rb ->
  exists ga gb,sf_relation M SFAnd d2 d1 ga /\ sf_relation M SFAnd ga ra ma /\
    sf_relation M SFAnd d2 domain gb /\ sf_relation M SFAnd gb rb mb.
Proof.
  intros HD HS1 HS2 HM HMA HMB HRA HRB.
  pose proof (source_domain_instance_zero M domain HD) as H0.
  pose proof (source_domain_instance_shift M domain (zeroM M) domain d1 HD H0 HS1) as H1.
  pose proof (source_domain_instance_shift M domain (code_numeral M 1) d1 d2 HD H1 HS2) as H2.
  destruct (source_guarded_matrix_schema_renaming M RepA domain rphi matrix ra ma d2 d1
    HD HM HMA HRA H2 H1) as [ga [HA GA]].
  destruct (source_guarded_matrix_schema_renaming M RepB domain rphi matrix rb mb d2 domain
    HD HM HMB HRB H2 H0) as [gb [HB GB]].
  exists ga,gb. auto.
Qed.

Print Assumptions source_domain_instance_renaming.
Print Assumptions source_guarded_matrix_schema_renaming.
Print Assumptions source_replacement_guarded_pair_shapes.
