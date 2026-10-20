(** Actual SepBody equals two cutoff1 insertions; its external carrier
    insertion is the third cutoff1 insertion, on arbitrary source codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded SourceBoundMonotone
  NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming RenamingSubstitution
  SourceSubstitutionComposition SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceQfFunctionality
  SchemaRenamingDescriptors SourceDomainInstances SourceRelativization SourceRelativizationSubstitution SourceRelativizationFunctionality.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_cutoff_twice_is_SepBody M phi first second k :
  source_bounded M phi k ->source_cutoff_shift M 1 phi first ->source_cutoff_shift M 1 first second ->
  schema_renaming M SepBody phi second.
Proof.
  intros HB(ab&ac&an&HA&HF)(bb&bc&bn&HBF&HS).
  unfold schema_renaming. apply(proj2(numerical_renaming_substitution M phi(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2)second)).
  rewrite descriptor_numeral_add.
  change(numerical_substitution M phi(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)second).
  apply(numerical_substitution_composition M phi k ab ac an(code_numeral M 2)bb bc bn(code_numeral M 2)
    (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)first second HB HF HS).
  intros i j v HI HJ HV.
  assert(EBase:addM M(code_numeral M 1)(code_numeral M 2)=code_numeral M 3).
  { change(addM M(succM M(zeroM M))(code_numeral M 2)=succM M(code_numeral M 2)).
    rewrite Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. }
  rewrite <- EBase.
  apply(proj1(renaming_substitution_lookup M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2)i v)).
  change(schema_lookup M SepBody i v).
  destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i) as[E|[idx E]];subst i.
  - pose proof(substitution_lookup_functional M ab ac an(code_numeral M 2)(zeroM M)j(zeroM M)HJ
      (source_cutoff_shift_map_fixed_lookup M 1 ab ac an HA 0)) as E. subst j.
    pose proof(substitution_lookup_functional M bb bc bn(code_numeral M 2)(zeroM M)v(zeroM M)HV
      (source_cutoff_shift_map_fixed_lookup M 1 bb bc bn HBF 0)) as E. subst v.
    apply(proj2(schema_lookup_first M SepBody(zeroM M))). reflexivity.
  - pose proof(substitution_lookup_functional M ab ac an(code_numeral M 2)(succM M idx)j(succM M(succM M idx))HJ
      (source_cutoff_shift_map_tail_lookup M 1 ab ac an idx HA)) as E. subst j.
    pose proof(substitution_lookup_functional M bb bc bn(code_numeral M 2)(succM M(succM M idx))v(succM M(succM M(succM M idx)))HV
      (source_cutoff_shift_map_tail_lookup M 1 bb bc bn(succM M idx)HBF)) as E. subst v.
    apply(proj2(schema_lookup_tail M SepBody(succM M idx)(succM M(succM M(succM M idx)))
      ltac:(intro Hbad;exact(coding_not_lt_zero M idx(proj1(coding_lt_succ_cancel M idx(zeroM M))Hbad))))).
    change(succM M(succM M(succM M idx))=addM M(succM M idx)(code_numeral M 2)).
    rewrite Arithmetic.add_succ,(Arithmetic.add_comm M idx(code_numeral M 2)).
    change(succM M(succM M(succM M idx))=succM M(addM M(succM M(succM M(zeroM M)))idx)).
    rewrite !Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
Qed.

Theorem source_SepBody_carrier_cutoff M phi body first second third k :
  source_bounded M phi(succM M k) ->schema_renaming M SepBody phi body ->
  source_cutoff_shift M 1 phi first ->source_cutoff_shift M 1 first second ->source_cutoff_shift M 1 second third ->
  source_cutoff_shift M 2 body third.
Proof.
  intros HB HBody H1 H2 H3.
  pose proof(source_cutoff_twice_is_SepBody M phi first second(succM M k)HB H1 H2) as HBody'.
  pose proof(numerical_renaming_functional M phi(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2)body second HBody HBody') as E. subst body.
  destruct(source_cutoff_shift_total M 2 second) as(q&HQ).
  pose proof(source_cutoff_one_two_commute M first second second q(succM M(succM M k))
    (source_cutoff_shift_bounded M 1 phi first k HB H1)H2 H2 HQ) as HFinal.
  pose proof(source_cutoff_shift_functional M 1 second q third HFinal H3) as E. now subst q.
Qed.

Theorem source_cutoff_relativization_to M depth domain f g rf rg :
  source_bounded M domain(code_numeral M 1) ->source_cutoff_shift M depth f g ->
  source_relativization M domain f rf ->source_relativization M domain g rg ->source_cutoff_shift M depth rf rg.
Proof.
  intros HD(b&c&n&HM&HS)HR HGraph.
  destruct(source_relativization_substitution_exists M f domain b c n(code_numeral M(S depth))g rf HD HS HR) as(s&HG&HSub).
  pose proof(source_relativization_functional M g domain s rg HG HGraph) as E. subst s.
  exists b,c,n. auto.
Qed.
Print Assumptions source_cutoff_twice_is_SepBody.
Print Assumptions source_SepBody_carrier_cutoff.
Print Assumptions source_cutoff_relativization_to.
