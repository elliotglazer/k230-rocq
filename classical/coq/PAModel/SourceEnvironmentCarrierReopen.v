(** Reopen the An representative and its quantified environment at
 explicit names above all internally many assignment slots. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceNumeralLift SourceEnvironmentCarrierRecipe SourceDefinabilityBounds SourceFiniteCutoffShift
 SourceRepresentativeRenaming SourceRepresentationRepresentativePoint SourceDnRepresentativeTransport SourceDn
 SourceEnvironmentCoverageNaming SourceNamedQuantifierRules SourceRenamingBounds
 NumericalRenamingMaps NumericalRenaming SchemaConstructorBounds.
Unset Implicit Arguments.
Theorem source_environment_carrier_point_name M first guard point r k:
 source_bounded M first k ->source_cutoff_shift M 1 first guard ->
 code_relation M(fun _=>guard)E_environment_carrier_point point ->
 exists member inner named,
 sf_relation M SFMember(zeroM M)(succM M r)member /\sf_relation M SFImpl guard member inner /\
 sf_relation M SFAll inner(zeroM M)named /\source_representative_renaming M r point named.
Proof.
 intros BF HGuard HPoint.
 destruct(code_relation_total M(E_sf SFMember(CEconst 0)(CEconst 1))(fun _=>guard))as(atom&HAtom).
 pose proof(proj1(schema_expression_graph M(fun _=>guard)SFMember(CEconst 0)(CEconst 1)
  (zeroM M)(code_numeral M 1)atom eq_refl eq_refl)HAtom)as HA.
 destruct(code_relation_total M(E_sf SFImpl(CEvar 0)(E_sf SFMember(CEconst 0)(CEconst 1)))(fun _=>guard))as(body&HBody).
 pose proof(proj1(schema_expression_graph M(fun _=>guard)SFImpl(CEvar 0)_ guard atom body eq_refl HAtom)HBody)as HB.
 pose proof(proj1(schema_expression_graph M(fun _=>guard)SFAll _ (CEconst 0)body(zeroM M)point HBody eq_refl)HPoint)as HQ.
 destruct(sf_relation_total M SFMember(zeroM M)(succM M r))as(member&HM).
 destruct(sf_relation_total M SFImpl guard member)as(inner&HI).
 destruct(sf_relation_total M SFAll inner(zeroM M))as(named&HN).
 destruct(renaming_lift_total M r r(code_numeral M 1)(zeroM M))as(b&c&n&HL).
 assert(HG:numerical_renaming M guard b c n(zeroM M)guard).
 { exact(source_representative_lift_fixes_cutoff_one M first guard k r b c n BF HGuard HL). }
 assert(HMemb:numerical_renaming M atom b c n(zeroM M)member).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 1)atom b c n(zeroM M)member HA)).
   exists(zeroM M),(succM M r). split.
   - exact(proj2(renaming_lift_head M r r(code_numeral M 1)(zeroM M)b c n(zeroM M)HL)eq_refl).
   - exact(conj(representative_lift_one M r b c n HL)HM). }
 assert(HIMap:numerical_renaming M body b c n(zeroM M)inner).
 { apply(proj2(numerical_renaming_binary M SFImpl guard atom body b c n(zeroM M)inner
   (or_intror(or_intror eq_refl))HB)). exists guard,member. exact(conj HG(conj HMemb HI)). }
 exists member,inner,named. refine(conj HM(conj HI(conj HN _))).
 apply(proj2(numerical_renaming_quantifier M true body point r r(code_numeral M 1)(zeroM M)named HQ)).
 exists b,c,n,inner. exact(conj HL(conj HIMap HN)).
Qed.
Theorem source_environment_carrier_reopen M count carrier named:
 source_environment_carrier_recipe M count carrier ->
 source_representative_renaming M(code_numeral M 2)carrier named ->
 exists environment first guard point member inner namedpoint,
 source_envf M count environment /\source_cutoff_shift M 1 environment first /\source_cutoff_shift M 1 first guard /\
 code_relation M(fun _=>guard)E_environment_carrier_point point /\source_dn M count point carrier /\
 sf_relation M SFMember(zeroM M)(succM M(succM M(succM M count)))member /\
 sf_relation M SFImpl guard member inner /\sf_relation M SFAll inner(zeroM M)namedpoint /\
 source_representative_renaming M(succM M(succM M count))point namedpoint /\
 source_dn M count namedpoint named.
Proof.
 intros(environment&first&guard&point&HE&H1&H2&HP&HD)HNamed.
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as BF.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count)BF H2)as BG.
 destruct(source_environment_carrier_point_name M first guard point(succM M(succM M count))
  (succM M(succM M count))BF H2 HP)as(member&inner&namedpoint&HM&HI&HN&HR).
 assert(BP:source_bounded M point(succM M(succM M count))).
 { assert(B:schema_expression_bound M(fun _=>guard)E_environment_carrier_point(succM M(succM M count))).
   { unfold E_environment_carrier_point. repeat schema_constructor_bound;try schema_small_index;exact BG. }
   exact(B point HP). }
 assert(BPAdd:source_bounded M point(addM M count(succM M(succM M(zeroM M))))).
 { rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero. exact BP. }
 assert(HRAdd:source_representative_renaming M(addM M(code_numeral M 2)count)point namedpoint).
 { change(source_representative_renaming M(addM M(succM M(succM M(zeroM M)))count)point namedpoint).
   rewrite !Arithmetic.add_succ,Arithmetic.add_zero. exact HR. }
 assert(HNot:~coding_lt M(code_numeral M 2)(code_numeral M 2)).
 { intro H. change(coding_lt M(succM M(succM M(zeroM M)))(succM M(succM M(zeroM M))))in H.
   exact(coding_not_lt_zero M(zeroM M)(proj1(coding_lt_succ_cancel M(zeroM M)(zeroM M))
    (proj1(coding_lt_succ_cancel M(succM M(zeroM M))(succM M(zeroM M)))H))). }
 pose proof(source_dn_representative_transport M count point carrier namedpoint named(code_numeral M 2)(zeroM M)
  BPAdd HNot HD HRAdd HNamed)as HDNamed.
 exists environment,first,guard,point,member,inner,namedpoint.
 exact(conj HE(conj H1(conj H2(conj HP(conj HD(conj HM(conj HI(conj HN(conj HR HDNamed))))))))).
Qed.
Print Assumptions source_environment_carrier_point_name.
Print Assumptions source_environment_carrier_reopen.
