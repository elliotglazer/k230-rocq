(** The open L Replacement derivation from genuine source certificates:
    raw guarded Replacement, the strong L-bound theorem, and a closed
    L-Separation image. All matrix and prefix codes are arbitrary internal. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourceBounded
 SchemaRenamingDescriptors SchemaRenamingBounds SourceRelativeSchemaInputs SourceReplacementGuardRenaming SourceReplacementFunctionality
 SourceFunctionalityShells SourceWFReplacementConstructor SourcePropositionalRebase SourceWFSeparationConstructor
 SourceRelativeSchemaConstructors SourceSchemaRelativization NumericalInstantiation SourceDomainInstances
 NumericalContexts NumericalContextRenaming NumericalEnvironments NumericalRenaming NumericalSourceFull SourceTraceBounds SourceProofWeakening SourceProofRenaming
 SourceContextTransport SourceClosedContextShift SourceContextProofHelpers SourceDerivedRules SourceQuantifierRules SourceUniversalPropositional
 ContextCombination SourceDomainContexts SourceGuardedDomainOpenIncluded SourceRelativization NumericalSetClosure SourceRelativizationBounds
 SourceLReplacementPsiR SourceLReplacementCutShells SourceLReplacementCutSelection SourceLReplacementBoundCut SourceLReplacementRangeCut
 SourceLReplacementShellRebase SourceLReplacementAllocation SourceLReplacementSeparationShift SourceGuardedLRange SourceFiniteCutoffShift.
Unset Implicit Arguments.
Theorem source_full_L_replacement_open_from_certificates M domain domain1 rphi matrix ra rb rc ma mb mc raw
 theta first second bound sepRaw sepClosed sepImage separation shiftedSeparation target
 gb gc gn db dc b c l count:
 source_bounded M domain(code_numeral M 1) ->source_formula_shift M domain domain1 ->
 source_bounded M rphi(succM M(succM M count)) ->relative_replacement_matrix M domain rphi matrix ->
 schema_renaming M RepA rphi ra ->schema_renaming M RepB rphi rb ->schema_renaming M RepC rphi rc ->
 schema_renaming M RepA matrix ma ->schema_renaming M RepB matrix mb ->schema_renaming M RepC matrix mc ->
 sf_replacement_constructor M ma mb mc raw ->sf_relative_replacement_constructor M domain ra rb rc target ->
 code_relation M(schema_env3 domain rc(zeroM M))(E_L_replacement_theta(CEvar 0)(CEvar 1))theta ->
 source_bounded M theta(succM M(succM M(succM M count))) ->
 source_bounded M first(succM M(succM M(succM M(succM M count)))) ->
 source_bounded M second(succM M(succM M(succM M(succM M(succM M count))))) ->
 source_cutoff_shift M 1 theta first ->source_cutoff_shift M 2 theta first ->
 source_cutoff_shift M 1 first second ->source_cutoff_shift M 2 first second ->source_cutoff_shift M 3 first second ->
 code_relation M(schema_env3 domain(zeroM M)(zeroM M))(E_L_cover_witness(CEvar 0))bound ->
 code_relation M(schema_env3 domain first(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))separation ->
 code_relation M(schema_env3 domain second(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))shiftedSeparation ->
 source_bounded M sepRaw(succM M count) ->all_prefix M(succM M count)sepRaw sepClosed ->
 source_relativization M domain sepRaw separation ->source_relativization M domain sepClosed sepImage ->
 context_bounded M gb gc gn(zeroM M) ->source_domain_context M domain count db dc ->
 context_union M gb gc gn db dc count b c l ->
 source_full_prv M gb gc gn raw ->source_full_prv M gb gc gn bound ->source_full_prv M gb gc gn sepImage ->
 source_full_prv M b c l target.
Proof.
 intros HD HDShift HRPhi HM HRA HRB HRC HMA HMB HMC HRaw HTarget HTheta BTheta BFirst BSecond
  H1 H1' H2 H2' H3 HBound HSep HShiftSep HBSep HPrefix HSepRel HClosedRel HClosed HTable HUnion PRaw PBound PSep.
 pose proof(schema_replacement_a_bound M rphi ra count HRPhi HRA)as BRA.
 pose proof(schema_replacement_b_bound M rphi rb count HRPhi HRB)as BRB.
 pose proof(schema_replacement_c_bound M rphi rc count HRPhi HRC)as BRC.
 pose proof(source_relative_replacement_constructor_bound M domain ra rb rc target count HD BRA BRB BRC HTarget)as BTarget.
 destruct(source_L_replacement_open_split M domain ra rb rc theta target HTheta HTarget)
  as(rf&rhs&guarded&witness&HRF&HImp&HAll&HGuard&HWitness).
 destruct(proj1(source_bounded_accept_binary M SFImpl rf rhs target count(or_intror(or_intror eq_refl))HImp)BTarget)as(BRF&BRhs).
 pose proof(proj1(source_bounded_accept_unary M SFAll guarded rhs count(or_introl eq_refl)HAll)BRhs)as BGuard.
 pose proof(proj2(proj1(source_bounded_accept_binary M SFImpl domain witness guarded(succM M count)
  (or_intror(or_intror eq_refl))HGuard)BGuard))as BWitness.
 pose proof(source_context_union_bounded M gb gc gn db dc count b c l count HUnion
  (context_bounded_monotone M gb gc gn(zeroM M)count HClosed(coding_zero_lt_succ M count))
  (source_domain_context_bounded M domain count db dc HD HTable))as HC.
 pose proof(context_union_left M gb gc gn db dc count b c l HUnion)as HBase.
 pose proof(context_union_right M gb gc gn db dc count b c l HUnion)as HDom.
 destruct(environment_cons_total M b c l rf)as(fb&fc&fn&HConsRF).
 pose proof(proj2(context_bounded_cons M b c l rf fb fc fn count HConsRF)(conj BRF HC))as HFC.
 assert(HFIn:context_included M b c l fb fc fn).
 { intros f HF. apply(proj2(context_member_cons M b c l rf fb fc fn f HConsRF));now right. }
 assert(PRF:source_full_prv M fb fc fn rf).
 { exact(source_full_cons_head M b c l rf fb fc fn count HConsRF BRF HFC). }
 unfold sf_replacement_constructor,E_sf_replacement in HRaw.
 destruct(schema_expression_split M _ SFImpl _ _ raw HRaw)as(nf&rawrhs&HNF&HRawRhs&HRawImp).
 pose proof(source_replacement_functionality_rebase M ma mb mc nf HNF)as HNF'.
 pose proof(source_full_guarded_replacement_functionality M fb fc fn count domain rphi matrix ra rb ma mb rf nf
  HFC HD BRA BRB HM HMA HMB HRA HRB HRF HNF' PRF)as PNF.
 pose proof(source_full_prv_weaken_bounded M gb gc gn fb fc fn raw count PRaw
  ltac:(intros f HF;exact(HFIn f(HBase f HF)))HFC)as PRaw'.
 pose proof(source_full_modus_ponens M fb fc fn nf rawrhs raw HRawImp PRaw' PNF)as PRawRhs.
 destruct(schema_expression_quantifier_split M _ SFAll _ rawrhs HRawRhs)as(rawex&HRawEx&HRawAll).
 destruct(context_shift_total M fb fc fn)as(fs&ft&HFShift).
 destruct(environment_cons_total M fs ft fn domain)as(ab&ac&an&HConsA).
 pose proof(context_shift_preserves_bound M fb fc fn fs ft count HFShift HFC)as HFSC.
 pose proof(proj2(context_bounded_cons M fs ft fn domain ab ac an(succM M count)HConsA)
  (conj(sr_domain_bound_succ M domain count HD)HFSC))as HAC.
 assert(HAIn:context_included M fs ft fn ab ac an).
 { intros f HF. apply(proj2(context_member_cons M fs ft fn domain ab ac an f HConsA));now right. }
 assert(HBaseA:context_included M gb gc gn ab ac an).
 { intros f HF. apply HAIn. exact(source_context_included_shift M gb gc gn fb fc fn gb gc fs ft
    ltac:(intros q HQ;exact(HFIn q(HBase q HQ)))(source_closed_context_shift_self M gb gc gn HClosed)HFShift f HF). }
 destruct(context_shift_total M db dc count)as(ds&dt&HDShiftTable).
 destruct(environment_cons_total M ds dt count domain)as(nb&nc&nn&HNewTable).
 assert(E:nn=succM M count)by exact(proj1 HNewTable). subst nn.
 pose proof(source_domain_context_cons_shift M domain count db dc ds dt nb nc(succM M count)
  HD HTable HDShiftTable HNewTable)as HCanonicalTable.
 pose proof(source_context_included_shift M db dc count fb fc fn ds dt fs ft
  ltac:(intros q HQ;exact(HFIn q(HDom q HQ)))HDShiftTable HFShift)as HShiftDom.
 pose proof(source_context_included_cons M ds dt count fs ft fn domain nb nc(succM M count)ab ac an
  HShiftDom HNewTable HConsA)as HTableIn.
 pose proof(source_full_guarded_domain_open_included M domain gb gc gn(succM M count)sepRaw separation sepClosed sepImage
  nb nc ab ac an(succM M count)HClosed HD HBSep HPrefix HSepRel HClosedRel HCanonicalTable HBaseA HTableIn HAC PSep)as PSeparation.
 pose proof(source_full_prv_weaken_bounded M fs ft fn ab ac an rawex(succM M count)
  (source_full_all_shift M fb fc fn rawex rawrhs fs ft HRawAll PRawRhs HFShift)HAIn HAC)as PRawEx.
 pose proof(source_domain_instance_zero M domain HD)as HD0.
 pose proof(source_domain_instance_shift M domain(zeroM M)domain domain1 HD HD0 HDShift)as HD1.
 destruct(source_guarded_matrix_schema_renaming M RepC domain rphi matrix rc mc domain domain1
  HD HM HMC HRC HD0 HD1)as(guards&HGuards&HMCGuard).
 pose proof(source_L_guarded_range_rebase M domain domain1 rc ma mb mc guards rawex HGuards HMCGuard HRawEx)as HRawEx'.
 destruct(code_relation_total M(E_sf_ex(E_L_range_profile(CEvar 0)(CEvar 1)1))(schema_env3 domain theta(zeroM M)))as(relativeRange&HRelRange).
 pose proof(source_full_guarded_L_range M domain domain1 rc theta rawex relativeRange ab ac an count HD HDShift BRC HAC
  HRawEx' HTheta HRelRange PRawEx)as PRelativeRange.
 pose proof(source_full_L_range_cut M domain theta first second relativeRange bound separation shiftedSeparation witness
  ab ac an gb gc gn(succM M count)HD HAC HClosed HBaseA BTheta BFirst BSecond H1 H1' H2 H2'
  HRelRange HBound HShiftSep(source_L_separation_law_shift M domain first second separation shiftedSeparation HD H3 HSep HShiftSep)
  HWitness PBound PSeparation PRelativeRange)as PWitness.
 assert(PGuard:source_full_prv M fs ft fn guarded).
 { exact(full_source_II M fs ft fn domain witness guarded ab ac an
    (ex_intro _ (succM M count)(conj BGuard HFSC))PWitness HConsA HGuard). }
 pose proof(full_source_AllI M fb fc fn guarded rhs fs ft(ex_intro _ count(conj BRhs HFC))PGuard HFShift HAll)as PRhs.
 exact(full_source_II M b c l rf rhs target fb fc fn(ex_intro _ count(conj BTarget HC))PRhs HConsRF HImp).
Qed.
Print Assumptions source_full_L_replacement_open_from_certificates.
