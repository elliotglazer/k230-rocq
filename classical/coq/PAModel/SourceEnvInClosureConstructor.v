(** Exact EnvF successor constructor under two separate fresh witnesses.
    This is a numerical syntax theorem for arbitrary internal matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceDefinabilityPrimitives
 SourceDefinabilityStep SourceEnvFScopedHole SourceEnvInClosureRoleMaps SourceShiftSpecialization SourceRenamingIdentity
 SourceRenamingDiamond NumericalRenamingMaps NumericalRenaming RawBinderRenaming SourceNamedQuantifierRules
 SourceFiniteParameters SourceFiniteParameterProofs SourceParameterIdentityCalibration SourceThreeParameterCommutation.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition EIC_ext_roles {A}(old new value:A)i:=match i with 0=>old|1=>new|_=>value end.
Definition EIC_ext_expression:=source_parameter_expression source_three_parameter_names source_def_extension021.
Lemma eic_role_zero M name padding:
 renaming_lookup M name name(code_numeral M 1)(code_numeral M padding)(zeroM M)name.
Proof. left. split;[apply coding_zero_lt_succ|apply beta_singleton]. Qed.
Lemma eic_role_positive M name padding i:i<>zeroM M->
 renaming_lookup M name name(code_numeral M 1)(code_numeral M padding)i(addM M i(code_numeral M padding)).
Proof.
 intro HN. right. split;[|reflexivity]. intro H. apply coding_lt_succ_cases in H.
 destruct H as[H|H];[exact(coding_not_lt_zero M i H)|contradiction].
Qed.
Lemma eic_lift_padded_previous M f first second named z db dc dn k:
 source_bounded M f k->source_def_step M true f first->
 source_low_parameter_shift M 2 f second->
 renaming_lift M z z(code_numeral M 1)(code_numeral M 2)db dc dn->
 numerical_renaming M second db dc dn(code_numeral M 2)named->source_low_parameter_shift M 4 f named.
Proof.
 intros BF unused HSecond HL HNamed.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  db dc dn(code_numeral M 2)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)second f named BF HSecond HId HNamed).
 intros i j l m HI HJ HM HI0.
 rewrite(renaming_lookup_functional M _ _ _ _ i l i HI0(source_empty_renaming_lookup M i)).
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_zero M 2))in HM.
   apply(proj1(renaming_lift_head M z z _ _ db dc dn m HL))in HM. subst m. apply low_parameter_lookup_zero.
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_nonzero M 2(succM M q)(env_role_nonzero M q)))in HM.
   replace(addM M(succM M q)(code_numeral M 2))with(succM M(succM M(succM M q)))in HM.
   2:{ rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
   destruct(renaming_lift_tail_inv M z z _ _ db dc dn(succM M(succM M q))m HL HM)as(v&HV&EV).
   rewrite(renaming_lookup_functional M _ _ _ _ _ v _ HV(eic_role_positive M z 2 _ (env_role_nonzero M(succM M q))))in EV.
   subst m. replace(succM M(addM M(succM M(succM M q))(code_numeral M 2)))
    with(addM M(succM M q)(code_numeral M 4)).
   + apply low_parameter_lookup_nonzero,env_role_nonzero.
   + rewrite(Arithmetic.add_comm M(succM M q)(code_numeral M 4)),
      (Arithmetic.add_comm M(succM M(succM M q))(code_numeral M 2)).
     cbn[code_numeral]. rewrite!Arithmetic.add_succ,!Arithmetic.add_zero. reflexivity.
Qed.
Theorem source_env_in_closure_named_constructor M f next previousNamed nextNamed extension nextbody e z k:
 source_bounded M f k->source_def_step M true f next->
 source_env_witness_renaming M e 3 f previousNamed->source_env_witness_renaming M z 2 next nextNamed->
 code_relation M(EIC_ext_roles e z(code_numeral M 3))EIC_ext_expression extension->
 sf_relation M SFAnd previousNamed extension nextbody->
 e<>z->code_numeral M 3<>e->
 (forall i,coding_lt M i k->i<>zeroM M->addM M i(code_numeral M 3)<>e)->
 source_named_quantifier M false e nextbody nextNamed.
Proof.
 intros BF HStep HP HN HExt HNextBody HEZ H3E HFresh.
 destruct(source_def_step_graph M true f next HStep)as(second&body&(first&H1&H2)&HBody&HNext).
 pose proof(source_low_parameter_shift_zero M f k BF)as H0.
 pose proof(source_low_parameter_shift_step M 0 f f first k BF H0 H1)as HL1.
 pose proof(source_low_parameter_shift_step M 1 f first second k BF HL1 H2)as HL2.
 apply(proj1(numerical_renaming_quantifier M false body next z z(code_numeral M 1)(code_numeral M 2)nextNamed HNext))in HN.
 destruct HN as(db&dc&dn&closedbody&HL&HClosed&HEx).
 apply(proj1(numerical_renaming_binary M SFAnd second _ body db dc dn(code_numeral M 2)closedbody(or_introl eq_refl)HBody))in HClosed.
 destruct HClosed as(closedprev&closedext&HCPrev&HCExt&HCBody).
 pose proof(eic_lift_padded_previous M f next second closedprev z db dc dn k BF HStep HL2 HL HCPrev)as HLow4.
 destruct(raw_binder_renaming_total M e)as(rb&rc&HRaw).
 pose proof(source_env_witness_closing M 3 f previousNamed closedprev e k rb rc BF HP HLow4 HRaw HFresh)as HPrevClose.
 destruct(code_relation_total M EIC_ext_expression(EIC_ext_roles(zeroM M)(succM M z)(code_numeral M 4)))as(ext&HExtClosed).
 assert(HExtIdentity:code_relation M(fun i=>code_numeral M i)EIC_ext_expression(code_numeral M(sf_encode source_def_extension021))).
 { apply source_parameter_identity_calibration. intros[|[|[|i]]];reflexivity. }
 assert(HExtLift:numerical_renaming M(code_numeral M(sf_encode source_def_extension021))db dc dn(code_numeral M 2)ext).
 { apply(source_three_parameter_renaming_commutation M source_def_extension021
    (fun i=>code_numeral M i)(EIC_ext_roles(zeroM M)(succM M z)(code_numeral M 4))
    _ ext db dc dn(code_numeral M 2));try assumption;[exact source_def_extension_bound|].
   intros[|[|[|i]]]HI;try lia;cbn[EIC_ext_roles].
   - apply(proj2(renaming_lift_head M z z _ _ db dc dn(zeroM M)HL)). reflexivity.
   - apply(proj2(renaming_lift_tail M z z _ _ db dc dn(zeroM M)z HL)). apply eic_role_zero.
   - change(renaming_lookup M db dc dn(code_numeral M 2)(succM M(code_numeral M 1))(succM M(code_numeral M 3))).
     apply(proj2(renaming_lift_tail M z z _ _ db dc dn(code_numeral M 1)(code_numeral M 3)HL)).
     pose proof(eic_role_positive M z 2 _ (env_role_nonzero M(zeroM M)))as HR.
     cbn[code_numeral]in HR. now rewrite Arithmetic.add_succ,Arithmetic.add_zero in HR. }
 rewrite(numerical_renaming_functional M _ db dc dn _ closedext ext HCExt HExtLift)in HCBody.
 assert(HExtClose:numerical_renaming M extension rb rc(succM M e)(code_numeral M 1)ext).
 { apply(source_three_parameter_renaming_commutation M source_def_extension021
    (EIC_ext_roles e z(code_numeral M 3))(EIC_ext_roles(zeroM M)(succM M z)(code_numeral M 4))
    extension ext rb rc(succM M e)(code_numeral M 1));try assumption;[exact source_def_extension_bound|].
   intros[|[|[|i]]]HI;try lia;cbn[EIC_ext_roles];apply(proj2(HRaw _ _)).
   - left;auto.
   - right. split;[intro E;exact(HEZ(eq_sym E))|reflexivity].
   - right;auto. }
 exists rb,rc,closedbody. split;[exact HRaw|]. split;[|exact HEx].
 apply(proj2(numerical_renaming_binary M SFAnd previousNamed extension nextbody rb rc(succM M e)(code_numeral M 1)closedbody
  (or_introl eq_refl)HNextBody)). exists closedprev,ext. auto.
Qed.
Print Assumptions source_env_in_closure_named_constructor.
