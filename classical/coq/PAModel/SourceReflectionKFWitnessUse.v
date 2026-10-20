(** Actual projection and specialization of the K-successor witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource NumericalInstantiation NumericalSourceFull
 SourceInstantiationConstructors SourceDerivedRules SourceConjunctionRules SourceHierarchySyntax
 SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionSubstitution SourceReflectionKFWitness.
Unset Implicit Arguments.
Theorem source_full_reflection_KF_witness_pc M domain level sb sc count K k w witness X lev all gb gc gn:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->
 source_LL_instance M k X lev ->source_piece_conjunction M domain level sb sc count w X all ->
 source_full_prv M gb gc gn witness ->source_full_prv M gb gc gn lev ->source_full_prv M gb gc gn all.
Proof.
 intros HD HL HV(member&next&lev0&pc0&point&universal&inner&HM&HN&HL0&HPC0&HP&HA&HI&HW)HLev HPC PW PL.
 pose proof(source_full_conjunction_right M gb gc gn member inner witness HW PW)as PI.
 pose proof(source_full_conjunction_right M gb gc gn next universal inner HI PI)as PAll.
 pose proof(source_LL_instance_instantiation M(succM M k)(zeroM M)lev0 k X lev X HL0 HLev
  (fun ub uc HH=>substitution_singleton_tail M ub uc k)(fun ub uc HH=>HH))as HIL.
 destruct(numerical_instantiation_total M pc0 X)as(pc1&ib&ic&HHead&HSub).
 pose proof(source_piece_conjunction_substitution M count domain level sb sc(succM M w)(zeroM M)pc0
  ib ic(code_numeral M 1)(zeroM M)w X pc1 HD HL HV HPC0 HSub(substitution_singleton_tail M ib ic w)HHead)as HPC1.
 assert(E:pc1=all)by(eapply source_piece_conjunction_functional;eassumption). subst pc1.
 assert(HIP:numerical_instantiation M pc0 X all)by(exists ib,ic;auto).
 destruct(sf_relation_total M SFImpl lev all)as(instance&HInstance).
 pose proof(source_instantiation_binary M SFImpl lev0 pc0 point X lev all instance
  (or_intror(or_intror eq_refl))HP HIL HIP HInstance)as HInst.
 pose proof(full_source_AllE M gb gc gn point universal X instance
  (source_wf_quantifier_instance M gb gc gn SFAll point universal X instance(or_introl eq_refl)HA
   (source_full_prv_wellformed M gb gc gn universal PAll)HInst)PAll HA HInst)as PInstance.
 exact(source_full_modus_ponens M gb gc gn lev all instance HInstance PInstance PL).
Qed.
Print Assumptions source_full_reflection_KF_witness_pc.
