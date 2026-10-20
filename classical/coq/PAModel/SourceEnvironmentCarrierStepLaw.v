(** Uniform An successor law. The actual Op3 head proof is transported
    through every internally coded assignment binder. No mathematical
    proof premise remains; operation existence is a separate next shell. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent
 SourceBounded SourceBoundMonotone SourceNumeralLift SourceFiniteParameters SourceFiniteParameterProofs SourceEnvironmentPointSlots SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierWitness
 SourceEnvironmentSuccessorHead SourceEnvironmentHeadTotal SourceEnvironmentOperationPadding SourceDnPaddedUnaryMap
 SourceRepresentativeRenaming SourceRepresentativeQuantifier SourceNamedQuantifierRules
 SourceDefinabilityIteration SourceDefinabilityBounds SourceDefinabilityStep SourceFiniteCutoffShift SourceQfFunctionality
 SourceDn SourceDnStep SourceDnBounds SourceDnIterationCommute SourceEnvFScopedHole
 NumericalRenaming SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SchemaConstructorBounds
 SourceEnvironmentHeadCalibration.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Theorem source_zfr_environment_carrier_step_law M count previous result named:
 source_environment_carrier_recipe M count previous ->
 source_environment_carrier_recipe M(succM M count)result ->
 source_representative_renaming M(code_numeral M 2)previous named ->
 exists op inner law,source_environment_operation_graph M(code_numeral M 2)op /\
 sf_relation M SFImpl named result inner /\sf_relation M SFImpl op inner law /\source_zfr_provable M law.
Proof.
 intros HPrevious HResult HNamed.
 destruct(source_environment_carrier_witness M count previous named HPrevious HNamed)
 as(environment&first&guard&original&coverage&namedguard&member&namedmember&body&namedbody&HE&H1&H2&HP&HD&HG&HM0&HMN&HB&HNB&HAll&HDC&BBody).
 destruct HResult as(next&nextfirst&nextguard&nextpoint&HNext&HNext1&HNext2&HNextPoint&HDNext).
 destruct(source_def_iteration_succ_forward M true count _ next HNext)as(prior&HPrior&HStep).
 assert(EEnv:prior=environment)by(eapply source_def_iteration_functional;eassumption). subst prior.
 destruct(source_environment_successor_head M count environment next nextfirst nextguard nextpoint
  (source_envf_bound M count environment HE)HStep HNext1 HNext2 HNextPoint)
 as(first'&deep&target&HFirst&HDeep&HTarget&HNextStep).
 assert(EFirst:first'=first)by(eapply source_cutoff_shift_functional;eassumption). subst first'.
 assert(HDTarget:source_dn M count target result).
 { apply source_dn_succ_first in HDNext. destruct HDNext as(other&HOther&HDTarget).
   assert(E:other=target)by(eapply source_dn_successor_functional;eassumption). now subst other. }
 set(k:=succM M(succM M(succM M count))).
 assert(KNot:~coding_lt M k k).
 { intro H. exact(@Peano.lt_neq(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)k k H eq_refl). }
 assert(Nonzero:succM M(succM M count)<>zeroM M).
 { intro E. exact(Model.zero_ne_succ M(succM M count)(eq_sym E)). }
 assert(HBodyName:source_representative_renaming M k body namedbody).
 { apply(proj2(numerical_renaming_binary M SFImpl first member body k k(code_numeral M 1)(zeroM M)namedbody
   (or_intror(or_intror eq_refl))HB)).
   exists namedguard,namedmember. split;[exact HG|]. split;[|exact HNB].
   apply(proj2(numerical_renaming_member M(zeroM M)(succM M(succM M count))member k k(code_numeral M 1)(zeroM M)namedmember HM0)).
   exists k,(succM M(succM M count)). exact(conj(representative_lookup_zero M k)
    (conj(representative_lookup_nonzero M k _ Nonzero)HMN)). }
 pose proof(source_representative_quantifier_bound M true body namedbody k k coverage BBody KNot HBodyName HAll)as BCoverage.
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as BFirst.
 assert(BFirstK:source_bounded M first k).
 { apply(source_bounded_monotone M first(succM M(succM M count))k BFirst).
   apply coding_lt_succ_cases. left. apply coding_lt_succ. }
 assert(KA:coding_lt M k(succM M k))by apply coding_lt_succ.
 assert(KE:coding_lt M k(succM M(succM M k))).
 { exact(coding_lt_trans M k(succM M k)(succM M(succM M k))KA(coding_lt_succ M(succM M k))). }
 assert(ANot:~coding_lt M(succM M k)k).
 { intro H. apply KNot. exact(coding_lt_trans M k(succM M k)k KA H). }
 assert(ENot:~coding_lt M(succM M(succM M k))k).
 { intro H. apply KNot. exact(coding_lt_trans M k(succM M(succM M k))k KE H). }
 assert(EP:succM M(succM M k)<>k).
 { intro E. apply KNot. now rewrite<-E at 2. }
 assert(AP:succM M k<>k).
 { intro E. apply KNot. now rewrite<-E at 2. }
 assert(AE:succM M k<>succM M(succM M k)).
 { exact(fun E=>@Peano.lt_neq(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)
   (succM M k)(succM M(succM M k))(coding_lt_succ M(succM M k))E). }
 assert(OneK:coding_lt M(code_numeral M 1)k).
 { unfold k. apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 destruct(source_zfr_environment_head_total M(succM M(succM M count))k(succM M(succM M k))(succM M k)
  first namedguard coverage namedmember namedbody deep target k BFirstK BCoverage
  (coding_lt_succ M(succM M(succM M count)))OneK(coding_zero_lt_succ M(succM M(succM M count)))
  KNot ENot ANot EP AP AE HG HDeep HMN HNB HAll HTarget)
 as(padded&point&proof&HFixed&HPoint&HProof&PProof).
 pose proof(proj1(source_environment_operation_fixed_graph M(environment_point_names M(succM M(succM M count))
  k(succM M k)(succM M(succM M k)))padded eq_refl eq_refl)HFixed)as HPadded.
 destruct(code_relation_total M(source_parameter_expression source_three_parameter_names environment_operation_source)
  (environment_operation_roles M(code_numeral M 2)))as(op&HOp).
 pose proof(source_environment_operation_padding M count op padded HOp HPadded)as HPad.
 assert(BOp:source_bounded M op(code_numeral M 3)).
 { exact(source_environment_operation_graph_bound M(code_numeral M 2)op(code_numeral M 3)
   (coding_lt_succ M(code_numeral M 2))(proj2(coding_lt_succ_cancel M(zeroM M)(code_numeral M 2))
    (coding_zero_lt_succ M(code_numeral M 1)))(coding_zero_lt_succ M(code_numeral M 2))HOp). }
 pose proof(source_cutoff_shift_bounded M 1 next nextfirst(succM M count)(source_envf_bound M(succM M count)next HNext)HNext1)as BNextFirst.
 pose proof(source_cutoff_shift_bounded M 1 nextfirst nextguard(succM M(succM M count))BNextFirst HNext2)as BNextGuard.
 assert(BNextPoint:source_bounded M nextpoint(succM M(succM M(succM M count)))).
 { assert(B:schema_expression_bound M(fun _=>nextguard)E_environment_carrier_point(succM M(succM M(succM M count)))).
   { unfold E_environment_carrier_point. repeat schema_constructor_bound;try schema_small_index;exact BNextGuard. }
   exact(B nextpoint HNextPoint). }
 pose proof(source_dn_successor_bounded M nextpoint target count BNextPoint HNextStep)as BTarget.
 assert(BTargetK:source_bounded M target k).
 { exact(source_bounded_monotone M target(succM M(succM M count))k BTarget
   (proj2(coding_lt_succ_cases M(succM M(succM M count))k)(or_introl(coding_lt_succ M(succM M(succM M count)))))). }
 assert(EAdd:addM M count(code_numeral M 3)=k).
 { rewrite Arithmetic.add_comm. change(addM M(succM M(succM M(succM M(zeroM M))))count=k).
   now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
 destruct(sf_relation_total M SFImpl named result)as(inner&HInner).
 destruct(sf_relation_total M SFImpl op inner)as(law&HLaw).
 exists op,inner,law. refine(conj HOp(conj HInner(conj HLaw _))).
 apply(proj1(source_zfr_descriptor_provable M law)).
 apply(source_descriptor_dn_padded_map M ZFRSourceDescriptor count op padded coverage target named result
  point proof inner law(code_numeral M 1)BOp).
 - change(source_bounded M coverage(addM M count(code_numeral M 3))). rewrite EAdd. exact BCoverage.
 - change(source_bounded M target(addM M count(code_numeral M 3))). rewrite EAdd. exact BTargetK.
 - exact HPad.
 - exact HDC.
 - exact HDTarget.
 - exact HPoint.
 - exact HProof.
 - exact HInner.
 - exact HLaw.
 - exact(proj2(source_zfr_descriptor_provable M proof)PProof).
Qed.
Print Assumptions source_zfr_environment_carrier_step_law.

