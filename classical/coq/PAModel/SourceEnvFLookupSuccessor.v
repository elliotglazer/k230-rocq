(** Genuine successor proof for arbitrary internally long EnvF lookup.
    The two actual witnesses are eliminated in the source proof calculus. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceFiniteCutoffShift SourceDefinabilityPrimitives SourceQuantifierRules NumericalInstantiation NumericalRenaming SourceDefinabilityIteration SourceDefinabilityBounds
 SourceEnvFLookupRecipe SourceEnvFLookupProfile SourceEnvFLookupProfileTransport SourceEnvFLookupIHRelocation
 SourceEnvFLookupProfileShell SourceEnvFLookupPoint SourceEnvFLookupBoundExistence SourceEnvFLookupFiniteProofs
 SourceEnvFDomainWitnessRecipe SourceEnvFDomainWitnessFixed SourceEnvFDomainWitnessMaps SourceEnvFDomainWitnessSyntax
 SourceEnvFDomainWitnessIH SourceEnvFDomainWitnessBounds SourceEnvFDomainWitnessInduction
 SourceNumFUniqueNames SourceNumFDistinctNames SourceNumFDistinctRecipe SourceZFRNumF SourceHierarchyShifts SourceDefinabilityLogicalStep
 SourceWitnessProofComposition SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Local Opaque code_numeral ew_domain ew_extension032 ew_extension143 source_env_profile.
Theorem source_zfr_env_lookup_successor M count:source_env_lookup_proof_at M count->source_env_lookup_proof_at M(succM M count).
Proof.
 intros IH k tail environment query result HLength HEnv HQuery(es&profile&inner&HES&HP&HInner&HResult).
 apply(succ_injective M)in HLength.
 apply source_def_iteration_succ in HEnv. destruct HEnv as(p&HPred&HEnvStep).
 pose proof(source_envf_bound M count p HPred)as BP.
 pose proof(source_numf_bound M k query HQuery)as BQuery.
 destruct(source_envf_witness_structure M p environment HEnvStep)as(p1&p2&p3&shifted&envbody&shiftedBody&envShift&H1&H2&H3&HShifted&HEnvBody&HEnvEx&HEnvShift&HShiftedBody&HEnvBodyShift).
 pose proof(numerical_renaming_functional M environment _ _ _ _ es envShift HES HEnvShift)as EE. subst es.
 destruct(numerical_instantiation_total M query(code_numeral M 1))as(query1&HQ1).
 destruct(numerical_instantiation_total M query(code_numeral M 2))as(query2&HQ2).
 pose proof(source_domain_shift_to M query(zeroM M)query query1 BQuery(source_unit_instantiation_self M query BQuery)HQ1)as HQueryShift1.
 pose proof(source_domain_shift_to M query(code_numeral M 1)query1 query2 BQuery HQ1 HQ2)as HQueryShift2.
 destruct(source_env_profile_total M(code_numeral M 2)(code_numeral M 1)(succM M(succM M(succM M tail))))as(profile1&HP1).
 destruct(source_env_profile_total M(code_numeral M 3)(code_numeral M 2)(succM M(succM M(succM M(succM M tail)))))as(profile2&HP2).
 pose proof(source_env_profile_shift M(code_numeral M 1)(zeroM M)(succM M(succM M tail))profile profile1 HP HP1)as HProfileShift1.
 pose proof(source_env_profile_shift M(code_numeral M 2)(code_numeral M 1)(succM M(succM M(succM M tail)))profile1 profile2 HP1 HP2)as HProfileShift2.
 destruct(sf_relation_total M SFImpl query1 profile1)as(inner1&HInner1).
 destruct(sf_relation_total M SFImpl query2 profile2)as(inner2&HInner2).
 pose proof(source_implication_shift_graph M query profile inner query1 profile1 inner1 HInner HInner1 HQueryShift1 HProfileShift1)as HInnerShift1.
 pose proof(source_implication_shift_graph M query1 profile1 inner1 query2 profile2 inner2 HInner1 HInner2 HQueryShift2 HProfileShift2)as HInnerShift2.
 destruct(source_numf_total M count)as(numeral&HNumeral).
 pose proof(source_numf_bound M count numeral HNumeral)as BNumeral.
 destruct(sf_relation_total M SFEx numeral(zeroM M))as(numEx&HNumEx).
 pose proof(source_zfr_numf_exists M count numeral numEx HNumeral HNumEx)as PNumEx.
 destruct(source_env_domain_witness_recipe_total M p numeral)as(oldDomain&HOldDomain).
 pose proof(source_zfr_env_domain_witness M count p numeral oldDomain HPred HNumeral HOldDomain)as POldDomain.
 destruct(sf_relation_total M SFImpl numeral(ew_domain_code M 1 0))as(domainInner&HDomainInner).
 destruct(sf_relation_total M SFImpl shifted domainInner)as(domain&HDomain).
 pose proof(source_zfr_env_domain_witness_ih M p numeral oldDomain p1 p2 p3 shifted domainInner domain count
  BP BNumeral HOldDomain H1 H2 H3 HShifted HDomainInner HDomain POldDomain)as PDomain.
 destruct(sf_relation_total M SFImpl shiftedBody inner2)as(deepTarget&HDeepTarget).
 destruct(sf_relation_total M SFImpl numeral deepTarget)as(point&HPoint).
 assert(PPoint:source_zfr_provable M point).
 { destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)tail)as[EZero|(t&ETail)].
   - subst tail. rewrite coding_add_zero_r in HLength. subst count.
     assert(EN:numeral=query).
     { eapply(source_def_iteration_functional M false k(code_numeral M(sf_encode source_def_empty)));eassumption. }
     subst numeral.
     change(source_env_profile M(code_numeral M 3)(code_numeral M 2)(code_numeral M 4)profile2)in HP2.
     destruct(source_zfr_env_lookup_profile_head_shell M profile2 HP2)as(equal&fixedInner&fixedTail&fixed&HEq&HFixedInner&HFixedTail&HFixed&PFixed).
     destruct(sf_relation_total M SFImpl query equal)as(uniqueInner&HUniqueInner).
     destruct(sf_relation_total M SFImpl query2 uniqueInner)as(unique&HUnique).
     pose proof(source_zfr_numf_unique_names M k query(code_numeral M 2)(zeroM M)query2 query equal uniqueInner unique
      HQuery HQ2(source_unit_instantiation_self M query BQuery)HEq HUniqueInner HUnique)as PUnique.
     exact(source_zfr_env_lookup_head_point M shifted query(ew_domain_code M 1 0)(code_numeral M(sf_encode ew_extension143))query2 equal profile2
      domainInner domain uniqueInner unique fixedInner fixedTail fixed shiftedBody inner2 deepTarget point
      HDomainInner HDomain HUniqueInner HUnique HFixedInner HFixedTail HFixed HShiftedBody HInner2 HDeepTarget HPoint PDomain PUnique PFixed).
   - subst tail. change(count=addM M k(succM M t))in HLength.
     assert(HOldLength:count=succM M(addM M k t)).
     { rewrite HLength. rewrite(coding_add_comm M k(succM M t)),(Arithmetic.add_succ M t k),(coding_add_comm M t k). reflexivity. }
     assert(HNE:k<>count).
     { assert(HLT:coding_lt M k count)by(rewrite HOldLength;apply coding_le_add).
       exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)k count HLT). }
     destruct(source_env_lookup_recipe_total M p query t)as(old&HOld).
     pose proof(IH k t p query old HOldLength HPred HQuery HOld)as POld.
     destruct(source_env_profile_total M(code_numeral M 1)(code_numeral M 2)(succM M(succM M(succM M(succM M(succM M t))))))as(oldProfile&HOldProfile).
     destruct(sf_relation_total M SFImpl query2 oldProfile)as(oldInner&HOldInner).
     destruct(sf_relation_total M SFImpl shifted oldInner)as(relocated&HRelocated).
     pose proof(source_zfr_env_lookup_ih_relocation M p query t old p1 p2 p3 shifted query2 oldProfile oldInner relocated count
      BP BQuery HOld H1 H2 H3 HShifted HQ2 HOldProfile HOldInner HRelocated POld)as PRelocated.
     destruct(source_zfr_env_lookup_profile_tail_shell M(succM M(succM M(succM M(succM M(succM M t)))))oldProfile profile2
      HOldProfile HP2)as(equal&neg&last&fixedInner&fixedTail&fixed&HEq&HNeg&HLast&HFixedInner&HFixedTail&HFixed&PFixed).
     destruct(sf_relation_total M SFImpl numeral neg)as(distinctInner&HDistinctInner).
     destruct(sf_relation_total M SFImpl query2 distinctInner)as(distinct&HDistinct).
     assert(PDistinct:source_zfr_provable M distinct).
     { apply(source_zfr_numf_distinct_uniform M k count query numeral(code_numeral M 2)(zeroM M)distinct HNE HQuery HNumeral).
       exists query2,numeral,equal,neg,distinctInner. repeat split;try assumption.
       exact(source_unit_instantiation_self M numeral BNumeral). }
     exact(source_zfr_env_lookup_tail_point M shifted numeral(ew_domain_code M 1 0)(code_numeral M(sf_encode ew_extension143))query2 equal profile2 oldProfile
      neg domainInner domain distinctInner distinct oldInner relocated last fixedInner fixedTail fixed shiftedBody inner2 deepTarget point
      HNeg HDomainInner HDomain HDistinctInner HDistinct HOldInner HRelocated HLast HFixedInner HFixedTail HFixed
      HShiftedBody HInner2 HDeepTarget HPoint PDomain PDistinct PRelocated PFixed). }
 destruct(sf_relation_total M SFImpl envbody inner1)as(target&HTarget).
 pose proof(source_implication_shift_graph M envbody inner1 target shiftedBody inner2 deepTarget HTarget HDeepTarget HEnvBodyShift HInnerShift2)as HTargetShift.
 assert(BEnvBody:source_has_bound M envbody).
 { apply(source_has_bound_binary_join M SFAnd p3 _ envbody(or_introl eq_refl)HEnvBody).
   -      (* p3 has the explicit three cutoff bounds, independent of lookup indices. *)
     pose proof(source_cutoff_shift_bounded M 1 p p1 count(source_envf_bound M count p HPred)H1)as B1.
     pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M count)B1 H2)as B2.
     pose proof(source_cutoff_shift_bounded M 1 p2 p3(succM M(succM M count))B2 H3)as B3. exact(ex_intro _ _ B3).
   - exists(code_numeral M 4). exact(proj1(ew_extension_bounds M)). }
 assert(BInner1:source_has_bound M inner1).
 { apply(source_has_bound_binary_join M SFImpl query1 profile1 inner1(or_intror(or_intror eq_refl))HInner1).
   - exact(source_unary_instance_has_bound M query(code_numeral M 1)query1 BQuery HQ1).
   - exact(source_profile_has_bound M _ _ _ profile1 HP1). }
 destruct(source_has_bound_binary_join M SFImpl envbody inner1 target(or_intror(or_intror eq_refl))HTarget BEnvBody BInner1)as(kt&BTarget).
 pose proof(ew_exists_bound M numeral numEx(code_numeral M 1)HNumEx BNumeral)as BNumEx.
 destruct(sf_relation_total M SFImpl numEx target)as(mapNum&HMapNum).
 pose proof(source_zfr_exists_implication M numeral numEx target deepTarget point mapNum(code_numeral M 1)kt BNumEx BTarget HNumEx HTargetShift HPoint HMapNum PPoint)as PMapNum.
 assert(PTarget:source_zfr_provable M target).
 { apply(proj1(source_zfr_descriptor_provable M target)).
   exact(source_descriptor_provable_mp M ZFRSourceDescriptor numEx target mapNum
    (proj2(source_zfr_descriptor_provable M numEx)PNumEx)(proj2(source_zfr_descriptor_provable M mapNum)PMapNum)HMapNum). }
 destruct(source_has_bound_ex_join M envbody envShift HEnvEx BEnvBody)as(ke&BEnvShift).
 assert(BInner:source_has_bound M inner).
 { apply(source_has_bound_binary_join M SFImpl query profile inner(or_intror(or_intror eq_refl))HInner).
   - exists(code_numeral M 1). exact BQuery.
   - exact(source_profile_has_bound M _ _ _ profile HP). }
 destruct BInner as(ki&BInner).
 exact(source_zfr_exists_implication M envbody envShift inner inner1 target result ke ki BEnvShift BInner HEnvEx HInnerShift1 HTarget HResult PTarget).
Qed.
Print Assumptions source_zfr_env_lookup_successor.
