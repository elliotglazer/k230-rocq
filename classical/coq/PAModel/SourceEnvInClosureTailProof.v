(** The actual predecessor theorem is reused with its parameter block
    beginning at4, leaving name3 free for the new head assignment. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift SourceBoundMonotone
 SourceDefinabilityPrimitives SourceDefinabilityBounds SourceEnvInClosureRecipe SourceEnvInClosureTailMaps
 SourceEnvFScopedHole SourceFiniteCutoffShift SourceQfFunctionality SourceCutoffShiftCommutation SourceCutoffShiftConstructors
 SourceCutoffQuantifiers SourcePropositionalRebase SchemaConstructorBounds SourceMembershipBlocks SourceNumFClosureRecipe
 SourceNumFClosureSyntax SourceRepresentationClosureRecipe SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors
 SourceZFRProvability NumericalRenaming.
Unset Implicit Arguments.
Local Opaque source_def_successor01 representation_closure_condition.
Theorem source_env_in_closure_spine M block shifted out:
 code_relation M(env_in_closure_values block shifted)E_env_in_closure out->exists body ex tail middle,
 sf_relation M SFAnd shifted(source_numf_closure_member M 3)body /\sf_relation M SFEx body(zeroM M)ex /\
 sf_relation M SFImpl block ex tail /\sf_relation M SFImpl(numf_closure_condition_code M)tail middle /\
 sf_relation M SFImpl(numf_closure_succ_code M)middle out.
Proof.
 intro HO. unfold E_env_in_closure in HO.
 destruct(schema_expression_split M _ SFImpl _ _ out HO)as(s&middle&HS&HM&HOut).
 change(s=numf_closure_succ_code M)in HS. subst s.
 destruct(schema_expression_split M _ SFImpl _ _ middle HM)as(c&tail&HC&HT&HMiddle).
 change(c=numf_closure_condition_code M)in HC. subst c.
 destruct(schema_expression_split M _ SFImpl _ _ tail HT)as(b&ex&HB&HE&HTail).
 change(b=block)in HB. subst b.
 destruct(schema_expression_split M _ SFEx _ _ ex HE)as(body&z&HBody&HZ&HEx).
 change(z=zeroM M)in HZ. subst z.
 destruct(schema_expression_split M _ SFAnd _ _ body HBody)as(p&m&HP&HMem&HAnd).
 change(p=shifted)in HP. subst p. change(m=source_numf_closure_member M 3)in HMem. subst m.
 exists body,ex,tail,middle. auto.
Qed.
Theorem source_env_in_closure_tail_cutoff M count environment block tail first second third fourth out result:
 source_envf M count environment->source_membership_block M(code_numeral M 3)(zeroM M)count block->
 source_membership_block M(code_numeral M 4)(zeroM M)count tail->
 source_cutoff_shift M 1 environment first->source_cutoff_shift M 1 first second->
 source_cutoff_shift M 1 second third->source_cutoff_shift M 1 third fourth->
 code_relation M(env_in_closure_values block third)E_env_in_closure out->
 code_relation M(env_in_closure_values tail fourth)E_env_in_closure result->source_cutoff_shift M 3 out result.
Proof.
 intros HE HB HT H1 H2 H3 H4 HO HR.
 pose proof(source_envf_bound M count environment HE)as BF.
 pose proof(source_low_parameter_shift_zero M environment(succM M count)BF)as HL0.
 pose proof(source_low_parameter_shift_step M 0 environment environment first(succM M count)BF HL0 H1)as HL1.
 pose proof(source_low_parameter_shift_step M 1 environment first second(succM M count)BF HL1 H2)as HL2.
 pose proof(source_low_parameter_shift_step M 2 environment second third(succM M count)BF HL2 H3)as HL3.
 pose proof(source_low_parameter_shift_step M 3 environment third fourth(succM M count)BF HL3 H4)as HL4.
 destruct(source_cutoff_shift_total M 4 third)as(actual&HA).
 pose proof(source_low_parameter_shift_boundary_insert M 3 environment third actual(succM M count)BF HL3 HA)as HL4'.
 assert(E:actual=fourth)by(eapply numerical_renaming_functional;[exact HL4'|exact HL4]). subst actual.
 destruct(source_env_in_closure_spine M block third out HO)as(body&ex&inner&middle&HBody&HEx&HInner&HMiddle&HOut).
 destruct(source_env_in_closure_spine M tail fourth result HR)as(body'&ex'&inner'&middle'&HBody'&HEx'&HInner'&HMiddle'&HResult).
 assert(BMember:source_bounded M(source_numf_closure_member M 3)(code_numeral M 4)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)_(code_numeral M 4)
    (or_introl eq_refl)(sf_make_numeral M SFMember 0 3))). split;[apply coding_zero_lt_succ|apply coding_lt_succ]. }
 pose proof(source_cutoff_shift_binary M 4 SFAnd third _ body fourth _ body'(or_introl eq_refl)HBody HBody' HA
  (source_cutoff_shift_fixes_bounded M 4 _ BMember))as HBodyCut.
 pose proof(source_cutoff_quantifier_join M 3 false body body' ex ex' HEx HEx' HBodyCut)as HExCut.
 pose proof(source_cutoff_shift_binary M 3 SFImpl block ex inner tail ex' inner'(or_intror(or_intror eq_refl))
  HInner HInner'(source_membership_block_tail_cutoff M count block tail HB HT)HExCut)as HInnerCut.
 assert(BC:source_bounded M(numf_closure_condition_code M)(code_numeral M 3)).
 { apply source_formula_numeral_bounded,representation_closure_finite_bound. }
 assert(BS:source_bounded M(numf_closure_succ_code M)(code_numeral M 3)).
 { apply(source_bounded_monotone M _(code_numeral M 2)_(numerical_def_successor_bound M)).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 pose proof(source_cutoff_shift_binary M 3 SFImpl _ inner middle _ inner' middle'(or_intror(or_intror eq_refl))
  HMiddle HMiddle'(source_cutoff_shift_fixes_bounded M 3 _ BC)HInnerCut)as HMiddleCut.
 exact(source_cutoff_shift_binary M 3 SFImpl _ middle out _ middle' result(or_intror(or_intror eq_refl))
  HOut HResult(source_cutoff_shift_fixes_bounded M 3 _ BS)HMiddleCut).
Qed.
Theorem source_zfr_env_in_closure_tail_total M count environment out:
 source_envf M count environment->source_env_in_closure_recipe M count environment out->source_zfr_provable M out->
 exists first second third fourth tail result,
 source_cutoff_shift M 1 environment first /\source_cutoff_shift M 1 first second /\
 source_cutoff_shift M 1 second third /\source_cutoff_shift M 1 third fourth /\
 source_membership_block M(code_numeral M 4)(zeroM M)count tail /\
 code_relation M(env_in_closure_values tail fourth)E_env_in_closure result /\source_zfr_provable M result.
Proof.
 intros HE(block&first&second&third&HB&H1&H2&H3&HO)PO.
 destruct(source_cutoff_shift_total M 1 third)as(fourth&H4).
 destruct(source_membership_block_total M(code_numeral M 4)(zeroM M)count)as(tail&HT).
 destruct(code_relation_total M E_env_in_closure(env_in_closure_values tail fourth))as(result&HR).
 pose proof(source_env_in_closure_tail_cutoff M count environment block tail first second third fourth out result
  HE HB HT H1 H2 H3 H4 HO HR)as(b&c&n&HM&HS).
 exists first,second,third,fourth,tail,result. refine(conj H1(conj H2(conj H3(conj H4(conj HT(conj HR _)))))).
 apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor out b c n(code_numeral M 1)result
  (proj2(source_zfr_descriptor_provable M out)PO)(source_cutoff_shift_map_renaming M 3 out result b c n HM HS)).
Qed.
Print Assumptions source_env_in_closure_tail_cutoff.
Print Assumptions source_zfr_env_in_closure_tail_total.
