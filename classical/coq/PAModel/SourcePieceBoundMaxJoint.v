(** The maximum-witness branch as an actual standalone ZFR implication.
    Both monotonicity proofs and their closed axiom contexts are generated. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded Pairing
  NumericalContexts NumericalEnvironments NumericalSourceFull NumericalInstantiation SourceInstantiationConstructors SourceTraceBounds
  SourceDomainInstances SourceOrdinalPredicate SourceRawSubset SourceRawSubsetBounds SourceHierarchySyntax
  SourcePieceClosure SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionMonotonicity
  SourcePieceMonotonicity SourcePieceBoundGoal SourcePieceBoundMaxPoint SourceFiniteProofContexts SourceProofWeakening
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceThreeConditions.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_pcf_max_joint M od1 od2 od sub1 sub2 member prev piece joint:=
  exists prevLeft prevBody pieceBody maxLeft maxBody pair,
    sf_relation M SFAnd od1 member prevLeft /\sf_relation M SFAnd prevLeft prev prevBody /\
    sf_relation M SFAnd od2 piece pieceBody /\sf_relation M SFAnd od sub1 maxLeft /\
    sf_relation M SFAnd maxLeft sub2 maxBody /\sf_relation M SFAnd prevBody pieceBody pair /\
    sf_relation M SFAnd pair maxBody joint.

Theorem source_full_piece_conjunction_components M b c l a d f:
  sf_relation M SFAnd a d f ->source_full_prv M b c l f ->
  source_full_prv M b c l a /\source_full_prv M b c l d.
Proof.
  intros HF HP. pose proof(source_full_prv_wellformed M b c l f HP) as HW. split.
  - exact(full_source_CE1 M b c l a d f(source_wf_binary_left M b c l SFAnd a d f(or_introl eq_refl)HF HW)HP HF).
  - exact(full_source_CE2 M b c l a d f(source_wf_binary_right M b c l SFAnd a d f(or_introl eq_refl)HF HW)HP HF).
Qed.

Ltac pcf_joint_bound:=first[assumption|match goal with
  H:sf_relation ?mm SFAnd ?a ?d ?f |-source_bounded ?mm ?f ?kk =>
    apply(proj2(source_bounded_accept_binary mm SFAnd a d f kk(or_introl eq_refl)H));split;pcf_joint_bound end].

Theorem source_zfr_pcf_bound_max_joint M domain level sb sc n count phi entry g X goal d1 d2 d
    od1 od2 od sub1 sub2 member prev piece joint implication k:
  source_bounded M domain(code_numeral M 1) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_piece_table_valid M sb sc(succM M n) ->coding_lt M g k ->coding_lt M X k ->
  coding_lt M d1 k ->coding_lt M d2 k ->coding_lt M d k ->
  source_pcf_bound_goal M domain level sb sc(succM M n)g X goal ->
  beta M sb sc n entry ->pair_graph M count phi entry ->
  numerical_instantiation M(source_ordinal_predicate_code M)d1 od1 ->
  numerical_instantiation M(source_ordinal_predicate_code M)d2 od2 ->
  numerical_instantiation M(source_ordinal_predicate_code M)d od ->
  source_raw_subset_graph M d1 d sub1 ->source_raw_subset_graph M d2 d sub2 ->sf_relation M SFMember g d1 member ->
  source_piece_conjunction M domain level sb sc n d1 X prev ->source_pc_instance M domain level count phi d2 X piece ->
  source_pcf_max_joint M od1 od2 od sub1 sub2 member prev piece joint ->sf_relation M SFImpl joint goal implication ->
  source_zfr_provable M implication.
Proof.
  intros HD HLevel HV HG HX HD1 HD2 HDk HGoal HEntry HCount HOD1 HOD2 HOD HS1 HS2 HMember
    HPrev HPiece(prevLeft&prevBody&pieceBody&maxLeft&maxBody&pair&HPL&HPB&HCB&HML&HMB&HPair&HJoint)HImp.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
  assert(HEntryMember:context_member M sb sc(succM M n)entry) by(exists n;split;[apply coding_lt_succ|exact HEntry]).
  pose proof(HV entry count phi HEntryMember HCount) as HB.
  destruct(source_piece_conjunction_total M domain level sb sc n d X) as(newPrev&HNewPrev).
  destruct(source_pc_instance_total M domain level count phi d X) as(newPiece&HNewPiece).
  destruct(source_piece_curried_total M od1 od sub1 prev newPrev) as(prevLaw&HPrevLaw).
  pose proof(source_zfr_piece_conjunction_monotonicity M domain level HD HLevel n sb sc d1 d X od1 od sub1 prev newPrev prevLaw k
    HPrefix HD1 HDk HX HOD1 HOD HS1 HPrev HNewPrev HPrevLaw) as PPrevLaw.
  destruct(source_piece_curried_total M od2 od sub2 piece newPiece) as(pieceLaw&HPieceLaw).
  pose proof(source_zfr_pc_monotonicity M domain level count phi d2 d X od2 od sub2 piece newPiece pieceLaw
    HD HB HLevel HOD2 HOD HS2 HPiece HNewPiece HPieceLaw) as PPieceLaw.
  assert(Premises:forall f,In f[prevLaw;pieceLaw] ->source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f[<-|[<-|[]]];[exact PPrevLaw|exact(proj2(source_zfr_descriptor_provable M pieceLaw)PPieceLaw)]. }
  destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor[prevLaw;pieceLaw]Premises) as(b&c&l&HCtx&PLaws).
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d1 od1 k(source_ordinal_predicate_bounded M)HD1 HOD1) as BOD1.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d2 od2 k(source_ordinal_predicate_bounded M)HD2 HOD2) as BOD2.
  pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)d od k(source_ordinal_predicate_bounded M)HDk HOD) as BOD.
  pose proof(source_raw_subset_bounded M d1 d sub1 k HD1 HDk HS1) as BS1.
  pose proof(source_raw_subset_bounded M d2 d sub2 k HD2 HDk HS2) as BS2.
  pose proof(proj2(source_bounded_accept_atom M SFMember g d1 member k(or_introl eq_refl)HMember)(conj HG HD1)) as BMember.
  pose proof(source_piece_conjunction_bounded M n domain level sb sc d1 X prev k HD HL HPrefix HD1 HX HPrev) as BPrev.
  pose proof(source_pc_instance_bounded M domain level count phi d2 X piece k HD HL HB HD2 HX HPiece) as BPiece.
  assert(BJoint:source_bounded M joint k) by pcf_joint_bound.
  pose proof(source_pcf_bound_goal_bounded M domain level sb sc(succM M n)g X goal k HD HL HV HG HX HGoal) as BGoal.
  destruct(environment_cons_total M b c l joint) as(ub&uc&un&HCons).
  pose proof(context_bounded_monotone M b c l(zeroM M)k(proj1 HCtx)(coding_zero_lt_succ M k)) as BCtx.
  pose proof(proj2(context_bounded_cons M b c l joint ub uc un k HCons)(conj BJoint BCtx)) as BNew.
  assert(PJoint:source_full_prv M ub uc un joint).
  { apply full_source_Ctx;[exists k;auto|]. apply(proj2(context_member_cons M b c l joint ub uc un joint HCons)). now left. }
  destruct(source_full_piece_conjunction_components M ub uc un pair maxBody joint HJoint PJoint) as[PPair PMaxBody].
  destruct(source_full_piece_conjunction_components M ub uc un prevBody pieceBody pair HPair PPair) as[PPrevBody PPieceBody].
  destruct(source_full_piece_conjunction_components M ub uc un prevLeft prev prevBody HPB PPrevBody) as[PPrevLeft PPrev].
  destruct(source_full_piece_conjunction_components M ub uc un od1 member prevLeft HPL PPrevLeft) as[POD1 PMember].
  destruct(source_full_piece_conjunction_components M ub uc un od2 piece pieceBody HCB PPieceBody) as[POD2 PPiece].
  destruct(source_full_piece_conjunction_components M ub uc un maxLeft sub2 maxBody HMB PMaxBody) as[PMaxLeft PS2].
  destruct(source_full_piece_conjunction_components M ub uc un od sub1 maxLeft HML PMaxLeft) as[POD PS1].
  assert(PL:forall f,In f[prevLaw;pieceLaw] ->source_full_prv M ub uc un f).
  { intros f HF. exact(source_full_prv_weaken_bounded M b c l ub uc un f k(PLaws f HF)
      (SourceLeastOrdinalWitness.source_cons_tail_inclusion M b c l joint ub uc un HCons)BNew). }
  destruct(sf_relation_total M SFMember g d) as(newMember&HNewMember).
  pose proof(source_full_pcf_bound_max_point M ub uc un domain level sb sc n count phi entry g X goal
    d1 d2 d od1 od2 od sub1 sub2 member newMember prev newPrev piece newPiece prevLaw pieceLaw k
    HD HL HV HG HX HD1 HD2 HDk BNew HGoal HEntry HCount HOD1 HOD2 HOD HS1 HS2 HMember HNewMember
    HPrev HNewPrev HPiece HNewPiece HPrevLaw HPieceLaw POD1 POD2 POD PS1 PS2 PMember PPrev PPiece
    (PL prevLaw(or_introl eq_refl))(PL pieceLaw(or_intror(or_introl eq_refl)))) as PGoal.
  exists b,c,l. split;[exact(proj1(source_zfr_descriptor_context M b c l)HCtx)|].
  exact(full_source_II M b c l joint goal implication ub uc un
    (ex_intro _ k(conj(proj2(source_bounded_accept_binary M SFImpl joint goal implication k
      (or_intror(or_intror eq_refl))HImp)(conj BJoint BGoal))BCtx))PGoal HCons HImp).
Qed.

Print Assumptions source_full_piece_conjunction_components.
Print Assumptions source_zfr_pcf_bound_max_joint.
