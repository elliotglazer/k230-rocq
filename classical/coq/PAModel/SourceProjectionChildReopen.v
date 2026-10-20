(** Reopen the actual child representation at the first assignment step.
    The remaining arbitrary-length Dn prefix is retained, with the child
    representative moved from0 to the hygienic count+3 role. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundMonotone FixedSourceBounds
 SourceRepresentationRecipe SourceRepresentationPointDataBound SourceRepresentationSuccessorHead SourceProjectionHeadImage
 SourceDefinabilityIteration SourceDefinabilityBounds SourceDefinabilityStep SourceFiniteCutoffShift SourceQfFunctionality
 SourceDn SourceDnStep SourceDnBounds SourceDnIterationCommute SourceDnRepresentativeTransport SourceRepresentativeRenaming
 SourceProjectionRepresentativeMaps SourceQuantifierMatrixScopes SourceSetRelativization SourceRenamingBounds NumericalRenamingMaps NumericalRenaming
 SourceEnvFScopedHole.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_projection_child_reopen M count f rep named:
 source_bounded M f(succM M count) ->source_representation_recipe M(succM M count)f rep ->
 source_representative_renaming M(code_numeral M 3)rep named ->
 exists environment first deep child relative originalhead namedhead,
 source_envf M count environment /\source_cutoff_shift M 1 environment first /\source_low_parameter_shift M 3 first deep /\
 source_quantifier_matrix M(code_numeral M 1)f child /\source_set_relativization M(code_numeral M 3)child relative /\
 code_relation M(representation_point_environment deep relative)E_representation_head_point originalhead /\
 code_relation M(schema_env3 deep relative(succM M(succM M(succM M(succM M(succM M count))))))E_projection_child_head_point namedhead /\
 source_representative_renaming M(succM M(succM M(succM M count)))originalhead namedhead /\
 source_dn M count namedhead named /\source_bounded M namedhead(succM M(succM M(succM M(succM M count)))).
Proof.
 intros BF HRep HNamed.
 destruct HRep as(next&nextfirst&nextguard&matrix&relative&point&HNext&H1&H2&HM&HR&HP&HD).
 destruct(source_def_iteration_succ_forward M true count _ next HNext)as(environment&HE&HStep).
 destruct(source_representation_successor_head M count environment next nextfirst nextguard f matrix relative point(succM M count)
  (source_envf_bound M count environment HE)HStep H1 H2 BF HM HR HP)
  as(first&deep&child&childrelative&originalhead&HFirst&HDeep&HChild&HChildRelative&HOriginal&HSuccessor).
 assert(HDOriginal:source_dn M count originalhead rep).
 { apply source_dn_succ_first in HD. destruct HD as(other&HOther&HD).
   assert(E:other=originalhead)by(eapply source_dn_successor_functional;eassumption). now subst other. }
 pose proof(source_representation_point_data_bound M(succM M count)f next nextfirst nextguard matrix relative point
  BF HNext H1 H2 HM HR HP)as BPoint.
 pose proof(source_dn_successor_bounded M point originalhead count BPoint HSuccessor)as BOriginal.
 set(r:=succM M(succM M(succM M count))).
 destruct(code_relation_total M E_projection_child_head_point(schema_env3 deep childrelative(succM M(succM M r))))as(namedhead&HNamedHead).
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)HFirst)as BFirst.
 pose proof(source_projection_head_representative_image M first deep f child childrelative originalhead namedhead
  (succM M(succM M count))(succM M count)r BFirst HDeep BF HChild HChildRelative HOriginal HNamedHead)as HImage.
 assert(BAdd:source_bounded M originalhead(addM M count(code_numeral M 2))).
 { rewrite Arithmetic.add_comm. cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero. exact BOriginal. }
 assert(RAdd:source_representative_renaming M(addM M(code_numeral M 3)count)originalhead namedhead).
 { cbn[code_numeral]. rewrite!Arithmetic.add_succ,Arithmetic.add_zero. exact HImage. }
 assert(Not:~coding_lt M(code_numeral M 3)(code_numeral M 2)).
 { intro H. apply(proj1(fixed_source_numeral_lt_iff M 3 2))in H. lia. }
 pose proof(source_dn_representative_transport M count originalhead rep namedhead named(code_numeral M 3)(zeroM M)
  BAdd Not HDOriginal RAdd HNamed)as HDNamed.
 assert(BNamed:source_bounded M namedhead(succM M r)).
 { apply(numerical_renaming_preserves_bound M originalhead r r(code_numeral M 1)(zeroM M)namedhead
   (succM M(succM M count))(succM M r)BOriginal HImage).
   intros i j HI HJ. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j r HJ(representative_lookup_zero M r)). apply coding_lt_succ.
   - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
     rewrite(renaming_lookup_functional M _ _ _ _ _ j(succM M q)HJ(representative_lookup_nonzero M r _ HN)).
     apply(coding_lt_trans M(succM M q)(succM M(succM M count))(succM M r)HI).
     exact(coding_lt_trans M(succM M(succM M count))r(succM M r)
      (coding_lt_succ M(succM M(succM M count)))(coding_lt_succ M r)). }
 exists environment,first,deep,child,childrelative,originalhead,namedhead.
 exact(conj HE(conj HFirst(conj HDeep(conj HChild(conj HChildRelative(conj HOriginal(conj HNamedHead(conj HImage(conj HDNamed BNamed))))))))).
Qed.
Print Assumptions source_projection_child_reopen.
