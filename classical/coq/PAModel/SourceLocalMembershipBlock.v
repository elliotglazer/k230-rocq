(** Actual proofs of a renamed internally finite membership block from
    the assigned parameter proofs. No parameter-length proof family is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions NumericalContexts NumericalEnvironments
 NumericalContextRenaming SetFormulaCodes SourceTraceBounds SourceBounded SourceBoundMonotone NumericalRenamingMaps NumericalRenaming
 SourceMembershipBlocks SourceMembershipBlockProofs SourceContextConjunction SourceContextConjunctionProofs
 SourceContextConjunctionRenaming SourceDnEliminationInvariant SourceLocalParameterAssignment NumericalSourceFull.
Unset Implicit Arguments.
Theorem source_full_local_membership_block M count pb pc A S C rb rc block mapped gb gc gn k:
 source_local_role_assignment M count pb pc A S C rb rc ->
 source_membership_block M(code_numeral M 3)(zeroM M)count block ->
 numerical_renaming M block rb rc(source_local_role_length M count)(zeroM M)mapped ->
 context_bounded M gb gc gn k ->source_dn_parameter_proofs M count pb pc A gb gc gn ->
 source_full_prv M gb gc gn mapped.
Proof.
 intros HRole(sb&sc&HMembers&HBlock)HR BC HProofs.
 destruct(context_renaming_total M sb sc count rb rc(source_local_role_length M count)(zeroM M))as(tb&tc&HT).
 destruct(source_context_conjunction_total M tb tc count)as(result&HResult).
 pose proof(source_context_conjunction_renaming M sb sc tb tc rb rc(source_local_role_length M count)(zeroM M)count
  block result HBlock HResult HT)as HR'.
 rewrite(numerical_renaming_functional M block rb rc(source_local_role_length M count)(zeroM M)mapped result HR HR').
 assert(BSource:context_bounded M sb sc count(source_local_role_length M count)).
 { apply(source_membership_context_bound M(code_numeral M 3)(zeroM M)count sb sc(source_local_role_length M count));[|apply coding_zero_lt_succ|exact HMembers].
   intros i HI. rewrite Arithmetic.add_comm. change(coding_lt M(addM M(succM M(succM M(succM M(zeroM M))))i)(source_local_role_length M count)).
   rewrite!Arithmetic.add_succ,Arithmetic.add_zero. unfold source_local_role_length.
   do 3 apply(proj2(coding_lt_succ_cancel M _ _)). exact HI. }
 assert(BTarget:context_bounded M tb tc count(succM M rb)).
 { apply(context_renaming_preserves_bound M sb sc count rb rc(source_local_role_length M count)(zeroM M)tb tc
    (source_local_role_length M count)(succM M rb)HT BSource).
   intros i j HI HJ. apply(proj1(renaming_lookup_inside M rb rc(source_local_role_length M count)(zeroM M)i j HI))in HJ.
   exact(remainder_le_dividend M rb(beta_modulus M rc i)j HJ). }
 set(bound:=addM M k(succM M rb)).
 assert(BTC:context_bounded M tb tc count bound).
 { apply(context_bounded_monotone M tb tc count(succM M rb)bound BTarget).
   unfold bound. rewrite Arithmetic.add_comm. apply coding_le_add. }
 assert(BGC:context_bounded M gb gc gn bound).
 { exact(context_bounded_monotone M gb gc gn k bound BC(coding_le_add M k(succM M rb))). }
 assert(HRows:forall h,context_member M tb tc count h ->source_full_prv M gb gc gn h).
 { intros h HH. apply(proj1(context_renaming_member_iff M sb sc count rb rc(source_local_role_length M count)(zeroM M)tb tc h HT))in HH.
 destruct HH as(original&[i[HI HB]]&HRO).
 destruct(proj1(numerical_renaming_member M(addM M i(code_numeral M 3))(zeroM M)original rb rc
  (source_local_role_length M count)(zeroM M)h(HMembers i original HI HB))HRO)as(x&y&HX&HY&HAtom).
 pose proof(source_local_role_zero M count pb pc A S C rb rc HRole)as HZero.
 rewrite(renaming_lookup_functional M _ _ _ _ (zeroM M)y A HY HZero)in HAtom.
 destruct(beta_total M pb pc i)as(value&HV).
 pose proof(source_local_role_parameter M count pb pc A S C rb rc i value HRole HI HV)as HValue.
 assert(EName:addM M i(code_numeral M 3)=succM M(succM M(succM M i))).
 { rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
 rewrite EName in HX. rewrite(renaming_lookup_functional M _ _ _ _ _ x value HX HValue)in HAtom.
 exact(HProofs i value h HI HV HAtom). }
 exact(proj2(source_context_conjunction_intro M count tb tc result gb gc gn bound HResult BTC BGC HRows)).
Qed.
Print Assumptions source_full_local_membership_block.
