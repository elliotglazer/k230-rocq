(** Literal actual source maximum shell, including both raw subset formulas. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceOrdinalMaxOld SourceOrdinalMaxFixed SourceFiniteParameters SourceFiniteNameParameters SourcePropositionalRebase
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceDomainInstances SourceSubsetParameterCalibration
  SourceRawSubset SourceZFRProvability NumericalInstantiation OldNamedSyntaxBridge.
From OldZFC Require Z_base.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_ordinal_max_shell M a b oa ob sa sb left body ex tail law :=
  numerical_instantiation M(source_ordinal_predicate_code M) a oa /\
  numerical_instantiation M(source_ordinal_predicate_code M) b ob /\
  source_raw_subset_graph M(succM M a)(zeroM M) sa /\source_raw_subset_graph M(succM M b)(zeroM M) sb /\
  sf_relation M SFAnd(source_ordinal_predicate_code M) sa left /\sf_relation M SFAnd left sb body /\
  sf_relation M SFEx body(zeroM M) ex /\sf_relation M SFImpl ob ex tail /\sf_relation M SFImpl oa tail law.

Theorem source_zfr_ordinal_max_shell M a b :exists oa ob sa sb left body ex tail law,
  source_ordinal_max_shell M a b oa ob sa sb left body ex tail law /\source_zfr_provable M law.
Proof.
  set(rho:=fun i:nat=>match i with 0=>a|_=>b end).
  destruct(code_relation_total M source_ordinal_max_expression rho) as(law&HLaw).
  pose proof(source_zfr_ordinal_max M rho law HLaw) as PLaw.
  unfold source_ordinal_max_expression,source_ordinal_max_law,old_ordinal_max_law in HLaw.
  change(code_relation M rho(E_sf SFImpl
    (source_parameter_expression(source_finite_parameter_names 2)(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
    (E_sf SFImpl(source_parameter_expression(source_finite_parameter_names 2)(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 1))))
      (E_sf SFEx(E_sf SFAnd(E_sf SFAnd
        (source_parameter_expression(source_parameter_up(source_finite_parameter_names 2))(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
        (source_parameter_expression(source_parameter_up(source_finite_parameter_names 2))(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))))
        (source_parameter_expression(source_parameter_up(source_finite_parameter_names 2))(isolated_formula(OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 0)))))
        (CEconst 0)))) law) in HLaw.
  destruct(schema_expression_split M rho _ _ _ law HLaw) as(oa&tail&HOA&HTail&HImpA).
  destruct(schema_expression_split M rho _ _ _ tail HTail) as(ob&ex&HOB&HEx&HImpB).
  destruct(schema_expression_split M rho _ _ _ ex HEx) as(body&z&HBody&HZ&HQuant).
  change(z=zeroM M) in HZ. subst z.
  destruct(schema_expression_split M rho _ _ _ body HBody) as(left&sb&HLeft&HSB&HAndB).
  destruct(schema_expression_split M rho _ _ _ left HLeft) as(ord&sa&HOrd&HSA&HAndA).
  assert(HOA':numerical_instantiation M(source_ordinal_predicate_code M) a oa).
  { exact(source_parameter_ordinal_instance M(source_finite_parameter_names 2)rho 0 a oa eq_refl HOA). }
  assert(HOB':numerical_instantiation M(source_ordinal_predicate_code M) b ob).
  { exact(source_parameter_ordinal_instance M(source_finite_parameter_names 2)rho 1 b ob eq_refl HOB). }
  assert(HOrd':numerical_instantiation M(source_ordinal_predicate_code M)(zeroM M)ord).
  { exact(source_parameter_ordinal_instance M(source_parameter_up(source_finite_parameter_names 2))rho 0(zeroM M)ord eq_refl HOrd). }
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(zeroM M) ord(source_ordinal_predicate_code M)
    HOrd'(source_domain_instance_zero M(source_ordinal_predicate_code M)(source_ordinal_predicate_bounded M))) as E. subst ord.
  assert(HNameA:code_relation M rho(source_parameter_up(source_finite_parameter_names 2) 1)(succM M a)).
  { exists a,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|exact(Arithmetic.succ_as_add M a)]. }
  assert(HNameB:code_relation M rho(source_parameter_up(source_finite_parameter_names 2) 2)(succM M b)).
  { exists b,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|exact(Arithmetic.succ_as_add M b)]. }
  pose proof(source_parameter_raw_subset M(source_parameter_up(source_finite_parameter_names 2))rho 1 0(succM M a)(zeroM M)sa HNameA eq_refl HSA) as HSubA.
  pose proof(source_parameter_raw_subset M(source_parameter_up(source_finite_parameter_names 2))rho 2 0(succM M b)(zeroM M)sb HNameB eq_refl HSB) as HSubB.
  exists oa,ob,sa,sb,left,body,ex,tail,law. split;[unfold source_ordinal_max_shell;repeat split;assumption|exact PLaw].
Qed.

Print Assumptions source_zfr_ordinal_max_shell.
