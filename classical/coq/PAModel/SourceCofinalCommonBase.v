(** Actual seed law and literal zero-count recipe calibration at arbitrary
    internally coded K and seed names. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceCofinalCommonBaseOld SourceCommonLevelBase SourceCofinalCommonPoint SourceCofinalCommonRecipe
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceFiniteParameters SourceFiniteNameParameters
 SourceOrdinalParameterCalibration SourceHierarchyCalibration SourceOrdinalPredicate SourceMembershipBlocks
 SourcePropositionalRebase SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Definition source_cofinal_common_seed_law:=isolated_formula old_cofinal_common_seed_law.
Definition source_cofinal_common_seed_expression:=
 source_parameter_expression(source_finite_parameter_names 2)source_cofinal_common_seed_law.
Definition source_cofinal_common_empty_current:=isolated_formula(old_cofinal_common_empty(@OC.var OB.sig_empty 0)).
Definition source_cofinal_common_empty_expression:=
 source_parameter_expression(source_finite_parameter_names 2)source_cofinal_common_empty_current.
Theorem source_zfr_cofinal_common_seed M rho out:
 code_relation M rho source_cofinal_common_seed_expression out ->source_zfr_provable M out.
Proof.
 intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_cofinal_common_seed_law 2 rho out).
 - apply(proj2(source_zfr_descriptor_provable M _)).
   exact(finite_old_zfr_proof_lift M old_L_background old_cofinal_common_seed_law
    old_L_background_valid old_cofinal_common_seed_proof).
 - exact HO.
Qed.
Local Opaque source_common_empty_ordinal source_common_empty_level source_ordinal_predicate_code.
Theorem source_cofinal_common_empty_parameter_graph M rho out start :
 code_relation M rho source_cofinal_common_empty_expression out ->
 source_cofinal_common_recipe M start(zeroM M)(rho 0)out.
Proof.
 intro H.
 set(names:=source_parameter_up(source_parameter_up(source_finite_parameter_names 2))).
 change(code_relation M rho(E_sf SFEx(E_sf SFEx(E_sf SFAnd
  (E_sf SFMember(names 1)(names 2))
  (E_sf SFAnd(E_sf SFAnd(source_parameter_expression names source_common_empty_ordinal)
   (source_parameter_expression names source_common_empty_level))(E_sf SFImpl(CEconst 0)(CEconst 0))))
  (CEconst 0))(CEconst 0))out)in H.
 destruct(schema_expression_split M rho _ _ _ out H)as(exY&z1&HE&HZ1&HO).
 change(z1=zeroM M)in HZ1. subst z1.
 destruct(schema_expression_split M rho _ _ _ exY HE)as(point&z2&HP&HZ2&HY).
 change(z2=zeroM M)in HZ2. subst z2.
 destruct(schema_expression_split M rho _ _ _ point HP)as(member&common&HM&HC&HF).
 destruct(schema_expression_split M rho _ _ _ common HC)as(pair&truth&HPar&HTruth&HCommon).
 destruct(schema_expression_split M rho _ _ _ pair HPar)as(ordinal&level&HOrd&HLevel&HPair).
 destruct(schema_expression_split M rho _ _ _ truth HTruth)as(z3&z4&HZ3&HZ4&HTrue).
 change(z3=zeroM M)in HZ3. change(z4=zeroM M)in HZ4. subst z3 z4.
 destruct(schema_expression_split M rho _ _ _ member HM)as(d&K&HD&HK&HMember).
 assert(HOne:code_relation M rho(names 1)(code_numeral M 1)).
 { change(code_relation M rho(CEadd(CEconst 0)(CEconst 1))(code_numeral M 1)).
   exists(zeroM M),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|].
   symmetry. rewrite(Arithmetic.add_comm M(zeroM M)(code_numeral M 1)). apply coding_add_zero_r. }
 assert(HZero:code_relation M rho(names 0)(zeroM M))by reflexivity.
 assert(HK':code_relation M rho(names 2)(succM M(succM M(rho 0)))).
 { change(code_relation M rho(CEadd(CEadd(CEvar 0)(CEconst 1))(CEconst 1))(succM M(succM M(rho 0)))).
   exists(succM M(rho 0)),(code_numeral M 1). split.
   - exists(rho 0),(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|]. apply Arithmetic.succ_as_add.
   - split;[reflexivity|]. apply Arithmetic.succ_as_add. }
 pose proof(code_relation_functional M(names 1)rho d(code_numeral M 1)HD HOne)as E. subst d.
 pose proof(code_relation_functional M(names 2)rho K(succM M(succM M(rho 0)))HK HK')as E. subst K.
 pose proof(source_parameter_ordinal_instance M names rho 1(code_numeral M 1)ordinal HOne HOrd)as HOrdinal.
 pose proof(source_parameter_LL_instance M names rho 1 0(code_numeral M 1)(zeroM M)level HOne HZero HLevel)as HLL.
 exists point,exY. split;[|auto]. exists common,member. split;[|auto].
 exists truth,ordinal,level,pair. split;[apply source_membership_block_zero;exact HTrue|].
 repeat first[assumption|split].
Qed.
Print Assumptions source_zfr_cofinal_common_seed.
Print Assumptions source_cofinal_common_empty_parameter_graph.
