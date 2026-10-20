(** Actual arbitrary-count Dn transport for existential representation.
    The sole remaining hypotheses describe syntax; the Op4 point proof is
    supplied, and no per-matrix source theorem is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundMonotone FixedSourceBounds
 SourceRepresentationRecipe SourceExistentialRecipe SourceProjectionChildReopen SourceProjectionCanonicalPoint SourceProjectionHeadImage SourceProjectionHeadTotal
 SourceQuantifierMatrixScopes SourceProjectionOperationPadding SourceProjectionProfilePoint SourceProjectionFiniteSyntax SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierFreshWitness
 SourceDefinabilityIteration SourceDefinabilityBounds SourceFiniteCutoffShift SourceQfFunctionality SourceDefinabilityStep SourceEnvFScopedHole SourceShiftSpecialization
 SourceNamedQuantifierRules SourceRepresentativeRenaming NumericalRenamingMaps NumericalRenaming SourceRenamingBounds SourceSetRelativization SourceSetRelativizationBounds
 SourceEnvironmentCoverageNaming SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceNumeralLift SourceDn SourceDnBounds SourceDnPaddedBinaryMap SourceDescriptorProvability SourceZFRProvability SourceSetTheoryDescriptors SchemaConstructorBounds.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_zfr_projection_dn_constructor M count f existential rep childrep namedchild carrier namedcarrier:
 source_bounded M existential count ->sf_relation M SFEx f(zeroM M)existential ->
 source_representation_recipe M count existential rep ->source_representation_recipe M(succM M count)f childrep ->
 source_representative_renaming M(code_numeral M 3)childrep namedchild ->
 source_environment_carrier_recipe M count carrier ->source_representative_renaming M(code_numeral M 2)carrier namedcarrier ->
 exists op inner body law,
 code_relation M(projection_outer_roles M)(source_parameter_expression(source_finite_parameter_names 4)projection_operation4)op /\
 sf_relation M SFImpl namedcarrier rep inner /\sf_relation M SFImpl namedchild inner body /\sf_relation M SFImpl op body law /\source_zfr_provable M law.
Proof.
 intros BEx HEx HR HChildRep HChildName HCarrier HCarrierName.
 pose proof(proj1(source_bounded_accept_unary M SFEx f existential count(or_intror eq_refl)HEx)BEx)as BF.
 set(k:=succM M(succM M(succM M(succM M count)))).
 set(p:=k). set(a:=succM M p). set(e:=succM M a).
 assert(NI:forall v,~coding_lt M v v).
 { intros v H. exact(@Peano.lt_neq(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)v v H eq_refl). }
 assert(B23:coding_lt M(succM M(succM M count))(succM M(succM M(succM M count))))by(apply coding_lt_succ).
 assert(B3K:coding_lt M(succM M(succM M(succM M count)))k)by(apply coding_lt_succ).
 assert(B2K:coding_lt M(succM M(succM M count))k)by(exact(coding_lt_trans M _ _ _ B23 B3K)).
 assert(KP:~coding_lt M p k)by(exact(NI k)).
 assert(HPA:coding_lt M p a)by(apply coding_lt_succ).
 assert(HAE:coding_lt M a e)by(apply coding_lt_succ).
 assert(KA:~coding_lt M a k).
 { intro H. apply(NI p). exact(coding_lt_trans M p a k HPA H). }
 assert(KE:~coding_lt M e k).
 { intro H. apply KA. exact(coding_lt_trans M a e k HAE H). }
 assert(HP3:~coding_lt M p(succM M(succM M(succM M count)))).
 { intro H. exact(KP(coding_lt_trans M _ _ _ H B3K)). }
 destruct(source_projection_child_reopen M count f childrep namedchild BF HChildRep HChildName)
  as(environment&first&deep&child&childrelative&originalhead&head&HE&HFirst&HDeep&HChildMatrix&HChildRel&HOriginalHead&HHead&HHeadName&HDHead&BHead).
 destruct(source_environment_carrier_fresh_witness M count carrier namedcarrier p HCarrier HCarrierName HP3)
  as(environment'&first'&guard&originalcarrier&coverage&namedguard&member&inAn&oldbody&coveragebody&HE'&HFirst'&HGuard&HOriginalCarrier&HDCarrier&HNamedGuard&HMember&HInAn&HOldBody&HCoverageBody&HCoverage&HDCoverage&BOldBody).
 assert(EEnv:environment'=environment)by(eapply source_def_iteration_functional;eassumption). subst environment'.
 assert(EFirst:first'=first)by(eapply source_cutoff_shift_functional;eassumption). subst first'.
 destruct(source_representation_existential_recipe M count f existential rep HEx HR)
  as(environment'&first'&guard'&parent&parentrelative&pair&relative&point&HEParent&HFirstParent&HGuardParent&HParentMatrix&HParentRel&HPair&HRelative&HPoint&HDPoint).
 assert(EEnv:environment'=environment)by(eapply source_def_iteration_functional;eassumption). subst environment'.
 assert(EFirst:first'=first)by(eapply source_cutoff_shift_functional;eassumption). subst first'.
 assert(EGuard:guard'=guard)by(eapply source_cutoff_shift_functional;eassumption). subst guard'.
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)HFirst)as BFirst.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count)BFirst HGuard)as BGuard.
 assert(HLowGuard:source_low_parameter_shift M 1 first guard).
 { pose proof(source_low_parameter_shift_zero M first _ BFirst)as HZero.
   exact(source_low_parameter_shift_step M 0 first first guard _ BFirst HZero HGuard). }
 assert(BFirstK:source_bounded M first k).
 { exact(source_bounded_monotone M first _ k BFirst(coding_lt_trans M _ _ _ B2K(coding_lt_succ M k))). }
 assert(BNamedGuard:source_bounded M namedguard(succM M p)).
 { apply(numerical_renaming_preserves_bound M first p p(code_numeral M 1)(zeroM M)namedguard _ _ BFirst HNamedGuard).
   intros i j HI HJ. destruct(@Peano.zero_or_succ(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[v ->]].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j p HJ(representative_lookup_zero M p)). apply coding_lt_succ.
   - assert(HN:succM M v<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M v(eq_sym E))).
     rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(representative_lookup_nonzero M p _ HN)).
     exact(coding_lt_trans M _ _ _ HI(coding_lt_trans M _ _ _ B2K(coding_lt_succ M k))). }


 assert(BFirst3:source_bounded M first(succM M(succM M(succM M count)))).
 { exact(source_bounded_monotone M first _ _ BFirst(proj2(coding_lt_succ_cases M _ _)(or_introl B23))). }
 destruct(source_environment_coverage_witness_total M first guard(succM M count)p(succM M(succM M(succM M count)))BFirst3 HGuard B23 HP3)
  as(ng&member'&inAn'&shiftedmember&oldbody'&coveragebody'&shiftedbody&coverage'&HNG&HM'&HIA'&HSM&HOB'&HCB'&HSB&HAll&HBodyName&HNamedAll&BBody).
 assert(E:ng=namedguard)by(eapply numerical_renaming_functional;eassumption). subst ng.
 assert(E:inAn'=inAn)by(eapply sf_relation_functional;eassumption). subst inAn'.
 assert(E:coveragebody'=coveragebody)by(eapply sf_relation_functional;eassumption). subst coveragebody'.
 assert(E:coverage'=coverage)by(eapply source_named_quantifier_functional;eassumption). subst coverage'.
 assert(BGuardK:source_bounded M guard k)by(exact(source_bounded_monotone M guard _ k BGuard(coding_lt_trans M _ _ _ B3K(coding_lt_succ M k)))).
 assert(BSM:source_bounded M shiftedmember k).
 { exact(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M(succM M(succM M count)))shiftedmember k(or_introl eq_refl)HSM)
  (conj(coding_lt_trans M _ _ _(coding_zero_lt_succ M(succM M(succM M count)))B3K)B3K)). }
 assert(BSB:source_bounded M shiftedbody k).
 { exact(proj2(source_bounded_accept_binary M SFImpl guard shiftedmember shiftedbody k(or_intror(or_intror eq_refl))HSB)(conj BGuardK BSM)). }
 assert(BCoverage3:source_bounded M coverage(succM M(succM M(succM M count)))).
 { exact(proj2(source_bounded_accept_unary M SFAll shiftedbody coverage(succM M(succM M(succM M count)))(or_introl eq_refl)HAll)BSB). }
 assert(BCoverage:source_bounded M coverage k).
 { exact(source_bounded_monotone M coverage _ k BCoverage3(proj2(coding_lt_succ_cases M _ _)(or_introl B3K))). }
 assert(BParent:source_bounded M parent k).
 { apply(numerical_renaming_preserves_bound M f(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)parent(succM M count)k BF HParentMatrix).
   intros i j HI HJ. destruct(@Peano.zero_or_succ(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[v ->]].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(source_one_role_zero_lookup M(zeroM M)(code_numeral M 3))).
     apply coding_zero_lt_succ.
   - assert(HN:succM M v<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M v(eq_sym E))).
     rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(source_one_role_positive_lookup M(zeroM M)(code_numeral M 3)_ HN)).
     rewrite Arithmetic.add_comm. cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
     do 3 apply coding_lt_succ_cancel. exact HI. }
 assert(ThreeK:coding_lt M(code_numeral M 3)k).
 { change(coding_lt M(succM M(succM M(succM M(zeroM M))))(succM M(succM M(succM M(succM M count))))).
   do 3 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 pose proof(source_set_relativization_preserves_bound M parent(code_numeral M 3)k parentrelative ThreeK BParent HParentRel)as BParentRel.
 assert(BPair:source_bounded M pair k).
 { apply(proj2(source_bounded_accept_binary M SFAnd(code_numeral M(sf_make SFMember 0 3))parentrelative pair k(or_introl eq_refl)HPair)).
   split;[|exact BParentRel]. apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)_ k(or_introl eq_refl)(sf_make_numeral M SFMember 0 3))).
   exact(conj(coding_zero_lt_succ M _)ThreeK). }
 assert(BRelative:source_bounded M relative(succM M(succM M(succM M count)))).
 { exact(proj2(source_bounded_accept_unary M SFEx pair relative _(or_intror eq_refl)HRelative)BPair). }
 assert(BPoint:source_bounded M point(succM M(succM M count))).
 { assert(B:schema_expression_bound M(representation_point_environment guard relative)(E_representation_point(CEvar 0)(CEvar 1))(succM M(succM M count))).
   { unfold E_representation_point,E_sf_iff. repeat schema_constructor_bound;try schema_small_index;assumption. }
   exact(B point HPoint). }
 assert(BPointK:source_bounded M point k).
 { exact(source_bounded_monotone M point _ k BPoint(coding_lt_trans M _ _ _ B2K(coding_lt_succ M k))). }
 assert(OneK:coding_lt M(code_numeral M 1)k).
 { exact(coding_lt_trans M _ _ _(proj2(fixed_source_numeral_lt_iff M 1 3)ltac:(lia))ThreeK). }
 assert(ZeroK:coding_lt M(zeroM M)k)by(apply coding_zero_lt_succ).
 assert(PQ:~coding_lt M p(succM M(succM M count))).
 { intro H. exact(KP(coding_lt_trans M _ _ _ H B2K)). }
 assert(AQ:~coding_lt M a(succM M(succM M count))).
 { intro H. exact(KA(coding_lt_trans M _ _ _ H B2K)). }
 assert(EQ:~coding_lt M e(succM M(succM M count))).
 { intro H. exact(KE(coding_lt_trans M _ _ _ H B2K)). }
 destruct(source_projection_canonical_point M f first deep guard child parent childrelative parentrelative pair relative namedguard head coverage inAn coveragebody point
  (succM M(succM M count))(succM M(succM M(succM M count)))p a e k(succM M count)
  BF(coding_zero_lt_succ M count)BFirstK BNamedGuard BHead BCoverage B2K B3K OneK ZeroK KP KE KA HPA HAE PQ AQ EQ
  HDeep HLowGuard HNamedGuard HChildMatrix HParentMatrix HChildRel HParentRel HPair HRelative HHead HPoint HInAn HCoverageBody HCoverage)
  as(padded&pointinner&pointbody&pointlaw&HOpPadded&HPointInner&HPointBody&HPointLaw&PPointLaw).
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 4)projection_operation4)(projection_outer_roles M))as(op&HOp).
 assert(HOpInner:code_relation M(projection_inner_roles M count)(source_parameter_expression(source_finite_parameter_names 4)projection_operation4)padded).
 { refine(proj1(source_parameter_graph_ext M 4 projection_operation4 projection_operation_bound
   (source_finite_parameter_names 4)(source_finite_parameter_names 4)
   (projection_five_values(succM M(succM M count))(succM M(succM M(succM M count)))(code_numeral M 1)(zeroM M)p)
   (projection_inner_roles M count)_ padded)HOpPadded).
   intros[|[|[|[|i]]]]v HI;try lia.
   - change(v=succM M(succM M count)<->v=addM M count(code_numeral M 2)).
     rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
   - change(v=succM M(succM M(succM M count))<->v=addM M count(code_numeral M 3)).
     rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
   - reflexivity.
   - reflexivity. }
 pose proof(source_projection_operation_padding M count projection_operation4 op padded projection_operation_bound HOp HOpInner)as HPad.
 destruct(sf_relation_total M SFImpl namedcarrier rep)as(inner&HInner).
 destruct(sf_relation_total M SFImpl namedchild inner)as(body&HBodyOut).
 destruct(sf_relation_total M SFImpl op body)as(law&HLaw).
 assert(BOp:source_bounded M op(code_numeral M 4)).
 { apply(source_parameter_graph_bounded M 4 projection_operation4 projection_operation_bound(source_finite_parameter_names 4)(projection_outer_roles M)(code_numeral M 4));[|exact HOp].
   intros[|[|[|[|i]]]]v HI HV;try lia.
   - change(v=code_numeral M 2)in HV. subst v. apply(proj2(fixed_source_numeral_lt_iff M 2 4));lia.
   - change(v=code_numeral M 3)in HV. subst v. apply(proj2(fixed_source_numeral_lt_iff M 3 4));lia.
   - change(v=code_numeral M 1)in HV. subst v. apply(proj2(fixed_source_numeral_lt_iff M 1 4));lia.
   - change(v=zeroM M)in HV. subst v. apply coding_zero_lt_succ. }
 assert(Expand:addM M count(succM M(succM M(code_numeral M 2)))=k).
 { rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
 assert(BHeadAdd:source_bounded M head(addM M count(succM M(succM M(code_numeral M 2)))))by(now rewrite Expand).
 assert(BCoverageAdd:source_bounded M coverage(addM M count(succM M(succM M(code_numeral M 2)))))by(now rewrite Expand).
 assert(BPointAdd:source_bounded M point(addM M count(succM M(succM M(code_numeral M 2)))))by(now rewrite Expand).
 pose proof(source_descriptor_dn_padded_binary_map M ZFRSourceDescriptor count op padded head coverage point namedchild namedcarrier rep
  pointinner pointbody pointlaw inner body law(code_numeral M 2)BOp BHeadAdd BCoverageAdd BPointAdd HPad HDHead HDCoverage HDPoint
  HPointInner HPointBody HPointLaw HInner HBodyOut HLaw(proj2(source_zfr_descriptor_provable M pointlaw)PPointLaw))as PLaw.
 exists op,inner,body,law. exact(conj HOp(conj HInner(conj HBodyOut(conj HLaw(proj1(source_zfr_descriptor_provable M law)PLaw))))).
Qed.
Print Assumptions source_zfr_projection_dn_constructor.
