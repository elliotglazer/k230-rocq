(** Allocate both witnesses and discharge every named-graph and
    freshness premise of the actual EnvF successor point theorem. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift SourceBounded
 SourceBoundMonotone SourceRenamingBounds SourceDefinabilityPrimitives SourceDefinabilityBounds SourceDefinabilityStep SourceFiniteCutoffShift
 SourceEnvFScopedHole SourceEnvInClosureRoleMaps SourceEnvInClosureConstructor SourceEnvInClosureSuccessorPoint
 SourceEnvInClosureWitnessShell SourceNumFClosureRecipe SourceNumFClosureSyntax SourceRepresentationClosureRecipe
 SourceRepresentativeRenaming SourceNamedCutoffQuantifiers SourceNamedQuantifierRules SourceNamedVacuity SourceNamedElimination
 SourceCutoffShiftConstructors SourceParameterGraphs SourceFiniteParameterProofs NumericalRenamingMaps NumericalRenaming SourcePropositionalTemplates
 SchemaConstructorBounds SourceZFRProvability.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition E_env_in_closure_point:=E_sf SFImpl(CEconst(sf_encode source_def_successor01))
 (E_sf SFImpl(CEconst(sf_encode representation_closure_condition))
  (E_sf SFImpl(CEvar 0)(E_sf SFImpl(CEvar 1)(CEvar 2)))).
Definition EIC_point_result_values {A}(head old new:A)i:=match i with 0=>head|1=>old|_=>new end.
Local Opaque source_def_successor01 representation_closure_condition source_def_extension021.
Theorem source_zfr_env_in_closure_point_total M count f next p1 p2 p3 p4 n1 n2 n3 oldbody oldex newbody newex:
 source_envf M count f->source_def_step M true f next->
 source_cutoff_shift M 1 f p1->source_cutoff_shift M 1 p1 p2->source_cutoff_shift M 1 p2 p3->source_cutoff_shift M 1 p3 p4->
 source_cutoff_shift M 1 next n1->source_cutoff_shift M 1 n1 n2->source_cutoff_shift M 1 n2 n3->
 sf_relation M SFAnd p4(source_numf_closure_member M 3)oldbody->sf_relation M SFEx oldbody(zeroM M)oldex->
 sf_relation M SFAnd n3(source_numf_closure_member M 3)newbody->sf_relation M SFEx newbody(zeroM M)newex->
 exists head result,sf_relation M SFMember(code_numeral M 3)(zeroM M)head /\
 code_relation M(EIC_point_result_values head oldex newex)E_env_in_closure_point result /\source_zfr_provable M result.
Proof.
 intros HF HStep H1 H2 H3 H4 HN1 HN2 HN3 HOldBody HOldEx HNewBody HNewEx.
 set(L:=succM M(succM M(succM M(succM M count)))). set(e:=L). set(z:=succM M e). set(B:=succM M z).
 pose proof(source_envf_bound M count f HF)as BF.
 pose proof(source_def_environment_step_bound M count f next BF HStep)as BNext.
 pose proof(source_cutoff_shift_bounded M 1 f p1 count BF H1)as BP1.
 pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M count)BP1 H2)as BP2.
 pose proof(source_cutoff_shift_bounded M 1 p2 p3(succM M(succM M count))BP2 H3)as BP3.
 change(source_bounded M p3 L)in BP3.
 pose proof(source_cutoff_shift_bounded M 1 next n1(succM M count)BNext HN1)as BN1.
 pose proof(source_cutoff_shift_bounded M 1 n1 n2(succM M(succM M count))BN1 HN2)as BN2.
 change(source_bounded M n2 L)in BN2.
 assert(HLZ:coding_lt M L z)by(apply coding_lt_succ).
 assert(HZB:coding_lt M z B)by(apply coding_lt_succ).
 assert(HLB:coding_lt M L B)by(exact(coding_lt_trans M L z B HLZ HZB)).
 assert(NL:~coding_lt M L L).
 { intro H. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)L L H eq_refl). }
 assert(HEZ:e<>z)by(exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)e z HLZ)).
 assert(Small:forall i,(i<4)%nat->coding_lt M(code_numeral M i)L).
 { intros[|[|[|[|i]]]]HI;try lia;unfold L;schema_small_index. }
 assert(SmallZ:forall i,(i<4)%nat->z<>code_numeral M i).
 { intros i HI E. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)
    (code_numeral M i)z(coding_lt_trans M _ L z(Small i HI)HLZ)(eq_sym E)). }
 assert(H3E:code_numeral M 3<>e)by(exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ e(Small 3 ltac:(lia)))).
 assert(Raise:forall a,source_bounded M a L->source_bounded M a B).
 { intros a BA. apply(source_bounded_monotone M a L B BA).
   exact(coding_lt_trans M L B(succM M B)HLB(coding_lt_succ M B)). }
 destruct(source_representative_renaming_total M e p3)as(previousNamed&HRP).
 destruct(source_representative_renaming_total M z n2)as(nextNamed&HRN).
 pose proof(source_low_parameter_shift_zero M f(succM M count)BF)as LP0.
 pose proof(source_low_parameter_shift_step M 0 f f p1(succM M count)BF LP0 H1)as LP1.
 pose proof(source_low_parameter_shift_step M 1 f p1 p2(succM M count)BF LP1 H2)as LP2.
 pose proof(source_low_parameter_shift_step M 2 f p2 p3(succM M count)BF LP2 H3)as LP3.
 pose proof(source_env_witness_low_composition M 3 f p3 previousNamed e(succM M count)BF LP3 HRP)as WP.
 pose proof(source_low_parameter_shift_zero M next(succM M(succM M count))BNext)as LN0.
 pose proof(source_low_parameter_shift_step M 0 next next n1(succM M(succM M count))BNext LN0 HN1)as LN1.
 pose proof(source_low_parameter_shift_step M 1 next n1 n2(succM M(succM M count))BNext LN1 HN2)as LN2.
 pose proof(source_env_witness_low_composition M 2 next n2 nextNamed z(succM M(succM M count))BNext LN2 HRN)as WN.
 assert(BPN:source_bounded M previousNamed z).
 { apply(numerical_renaming_preserves_bound M p3 e e(code_numeral M 1)(zeroM M)previousNamed L z BP3 HRP).
   intros i j HI HJ. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j e HJ(representative_lookup_zero M e)). exact HLZ.
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(representative_lookup_nonzero M e _ (env_role_nonzero M q))).
     exact(coding_lt_trans M _ L z HI HLZ). }
 assert(BNN:source_bounded M nextNamed B).
 { apply(numerical_renaming_preserves_bound M n2 z z(code_numeral M 1)(zeroM M)nextNamed L B BN2 HRN).
   intros i j HI HJ. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j z HJ(representative_lookup_zero M z)). exact HZB.
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(representative_lookup_nonzero M z _ (env_role_nonzero M q))).
     exact(coding_lt_trans M _ L B HI HLB). }
 destruct(sf_relation_total M SFMember e(code_numeral M 2))as(oldmem&HOldMem).
 destruct(sf_relation_total M SFMember z(code_numeral M 2))as(newmem&HNewMem).
 destruct(sf_relation_total M SFMember(code_numeral M 3)(zeroM M))as(head&HHead).
 destruct(code_relation_total M EIC_ext_expression(EIC_ext_roles e z(code_numeral M 3)))as(extension&HExt).
 destruct(sf_relation_total M SFAnd previousNamed oldmem)as(oldNamedBody&HOldNamedBody).
 destruct(sf_relation_total M SFAnd nextNamed newmem)as(targetNamedBody&HTargetNamedBody).
 destruct(sf_relation_total M SFAnd p3(source_numf_closure_member M 2))as(oldBare&HOldBare).
 destruct(sf_relation_total M SFAnd n2(source_numf_closure_member M 2))as(newBare&HNewBare).
 assert(BM2:source_bounded M(source_numf_closure_member M 2)L).
 { apply source_numf_closure_member_bounded;[exact(Small 0 ltac:(lia))|exact(Small 2 ltac:(lia))]. }
 assert(BOBare:source_bounded M oldBare L)by(exact(proj2(source_bounded_accept_binary M SFAnd p3 _ oldBare L(or_introl eq_refl)HOldBare)(conj BP3 BM2))).
 assert(BNBare:source_bounded M newBare L)by(exact(proj2(source_bounded_accept_binary M SFAnd n2 _ newBare L(or_introl eq_refl)HNewBare)(conj BN2 BM2))).
 pose proof(source_cutoff_shift_binary M 1 SFAnd p3 _ oldBare p4 _ oldbody(or_introl eq_refl)HOldBare HOldBody H4(source_numf_closure_member_cutoff M 1))as HOCut.
 pose proof(source_cutoff_shift_binary M 1 SFAnd n2 _ newBare n3 _ newbody(or_introl eq_refl)HNewBare HNewBody HN3(source_numf_closure_member_cutoff M 1))as HNCut.
 assert(HOldName:source_representative_renaming M e oldBare oldNamedBody).
 { apply(proj2(numerical_renaming_binary M SFAnd p3 _ oldBare e e(code_numeral M 1)(zeroM M)oldNamedBody(or_introl eq_refl)HOldBare)).
   exists previousNamed,oldmem. split;[exact HRP|]. split;[|exact HOldNamedBody].
   apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2)_ e e(code_numeral M 1)(zeroM M)oldmem(source_numf_closure_member_graph M 2))).
   exists e,(code_numeral M 2). split;[apply representative_lookup_zero|].
   split;[apply representative_lookup_nonzero;apply env_role_nonzero|exact HOldMem]. }
 assert(HNewName:source_representative_renaming M z newBare targetNamedBody).
 { apply(proj2(numerical_renaming_binary M SFAnd n2 _ newBare z z(code_numeral M 1)(zeroM M)targetNamedBody(or_introl eq_refl)HNewBare)).
   exists nextNamed,newmem. split;[exact HRN|]. split;[|exact HTargetNamedBody].
   apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2)_ z z(code_numeral M 1)(zeroM M)newmem(source_numf_closure_member_graph M 2))).
   exists z,(code_numeral M 2). split;[apply representative_lookup_zero|].
   split;[apply representative_lookup_nonzero;apply env_role_nonzero|exact HNewMem]. }
 pose proof(source_named_fresh_quantifier_cutoff M false oldBare oldNamedBody e L oldbody oldex BOBare NL HOldName HOCut HOldEx)as QOld.
 assert(NZ:~coding_lt M z L)by(intro H;apply NL;exact(coding_lt_trans M L z L HLZ H)).
 pose proof(source_named_fresh_quantifier_cutoff M false newBare targetNamedBody z L newbody newex BNBare NZ HNewName HNCut HNewEx)as QNew.
 pose proof(source_named_quantifier_bound M false(zeroM M)oldBare oldex L BOBare(source_named_zero_quantifier_cutoff M false oldBare oldbody oldex HOCut HOldEx))as BOEx.
 pose proof(source_named_quantifier_bound M false(zeroM M)newBare newex L BNBare(source_named_zero_quantifier_cutoff M false newBare newbody newex HNCut HNewEx))as BNEx.
 assert(BS:source_bounded M(numf_closure_succ_code M)L).
 { apply(source_bounded_monotone M _(code_numeral M 2)L(numerical_def_successor_bound M)).
   exact(coding_lt_trans M _ L(succM M L)(Small 2 ltac:(lia))(coding_lt_succ M L)). }
 assert(BC:source_bounded M(numf_closure_condition_code M)L).
 { apply(source_bounded_monotone M _(code_numeral M 3)L).
   - apply source_formula_numeral_bounded,representation_closure_finite_bound.
   - exact(coding_lt_trans M _ L(succM M L)(Small 3 ltac:(lia))(coding_lt_succ M L)). }
 assert(BHead:source_bounded M head L)by(exact(proj2(source_bounded_accept_atom M SFMember _ _ head L(or_introl eq_refl)HHead)(conj(Small 3 ltac:(lia))(Small 0 ltac:(lia))))).
 assert(BOMem:source_bounded M oldmem B)by(exact(proj2(source_bounded_accept_atom M SFMember e _ oldmem B(or_introl eq_refl)HOldMem)(conj HLB(coding_lt_trans M _ L B(Small 2 ltac:(lia))HLB)))).
 assert(BNMem:source_bounded M newmem B)by(exact(proj2(source_bounded_accept_atom M SFMember z _ newmem B(or_introl eq_refl)HNewMem)(conj HZB(coding_lt_trans M _ L B(Small 2 ltac:(lia))HLB)))).
 assert(BExt:source_bounded M extension B).
 { apply(source_parameter_graph_bounded M 3 source_def_extension021 source_def_extension_bound source_three_parameter_names(EIC_ext_roles e z(code_numeral M 3))B);[|exact HExt].
   intros[|[|[|i]]]v HI HV;try lia.
   - change(v=e)in HV. subst v. exact HLB.
   - change(v=z)in HV. subst v. exact HZB.
   - change(v=code_numeral M 3)in HV. subst v. exact(coding_lt_trans M _ L B(Small 3 ltac:(lia))HLB). }
 set(values:=EIC_point_values M oldmem head previousNamed extension newmem nextNamed oldex newex(zeroM M)).
 assert(BValues:forall i,source_bounded M(values i)B).
 { intros[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]];cbn[values EIC_point_values].
   - exact(Raise _ BS). - exact(Raise _ BC). - exact BOMem. - exact(Raise _ BHead).
   - apply(source_bounded_monotone M previousNamed z B BPN). exact(coding_lt_trans M z B(succM M B)HZB(coding_lt_succ M B)).
   - exact BExt. - exact BNMem. - exact BNN. - exact(Raise _ BNEx). - apply source_bounded_accept_falsity.
   - exact(Raise _ BOEx). - apply source_bounded_accept_falsity. }
 destruct(code_relation_total M E_env_in_closure_point(EIC_point_result_values head oldex newex))as(result&GResult).
 exists head,result. refine(conj HHead(conj GResult _)).
 apply(source_zfr_env_in_closure_successor_point M f next e z(succM M count)B previousNamed nextNamed oldmem head newmem extension
  oldNamedBody targetNamedBody oldex newex result BF HStep WP WN HOldMem HHead HNewMem HExt HOldNamedBody HTargetNamedBody QOld QNew BValues).
 - apply(source_named_vacuous_above_bound M previousNamed z z BPN),coding_lt_succ.
 - apply(source_named_vacuous_above_bound M newex z L BNEx). exact(coding_lt_trans M L z(succM M z)HLZ(coding_lt_succ M z)).
 - apply(source_named_vacuous_above_bound M _ e L BS). exact HLZ.
 - apply(source_named_vacuous_above_bound M _ e L BC). exact HLZ.
 - apply(source_named_vacuous_above_bound M _ e L BHead). exact HLZ.
 - apply(source_named_vacuous_above_bound M _ e L BNEx). exact HLZ.
 - exact HEZ. - exact H3E. - exact(SmallZ 0 ltac:(lia)). - exact(SmallZ 1 ltac:(lia)).
 - exact(SmallZ 2 ltac:(lia)). - exact(SmallZ 3 ltac:(lia)).
 - intros i HI HN E.
   assert(HLt:coding_lt M(addM M i(code_numeral M 3))e).
   { unfold e,L. rewrite(Arithmetic.add_comm M i(code_numeral M 3)).
     cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero.
     do 3 apply coding_lt_succ_cancel. exact HI. }
   exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)_ e HLt E).
 - intro ex. exact GResult.
Qed.
Print Assumptions source_zfr_env_in_closure_point_total.
