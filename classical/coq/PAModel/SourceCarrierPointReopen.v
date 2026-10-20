(** Reopen the assignment carrier at any exterior role at least2.
    The environment and both guard insertions are preserved literally. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierReopen SourceDefinabilityBounds SourceFiniteCutoffShift
 SourceRepresentativeRenaming SourceDnRepresentativeTransport SourceDn SchemaConstructorBounds.
Unset Implicit Arguments.
Theorem source_carrier_point_reopen M count environment first guard point carrier r named:
 source_envf M count environment->source_cutoff_shift M 1 environment first->source_cutoff_shift M 1 first guard->
 code_relation M(fun _=>guard)E_environment_carrier_point point->source_dn M count point carrier->
 ~coding_lt M r(code_numeral M 2)->source_representative_renaming M r carrier named->
 exists member inner namedpoint,sf_relation M SFMember(zeroM M)(succM M(addM M r count))member/\
 sf_relation M SFImpl guard member inner/\sf_relation M SFAll inner(zeroM M)namedpoint/\
 source_representative_renaming M(addM M r count)point namedpoint/\source_dn M count namedpoint named.
Proof.
 intros HE H1 H2 HP HD HR HNamed.
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as BF.
 pose proof(source_cutoff_shift_bounded M 1 first guard(succM M count)BF H2)as BG.
 destruct(source_environment_carrier_point_name M first guard point(addM M r count)(succM M(succM M count))BF H2 HP)
  as(member&inner&namedpoint&HM&HI&HN&HPoint).
 assert(BP:source_bounded M point(succM M(succM M count))).
 { assert(B:schema_expression_bound M(fun _=>guard)E_environment_carrier_point(succM M(succM M count))).
   { unfold E_environment_carrier_point. repeat schema_constructor_bound;try schema_small_index;exact BG. }
   exact(B point HP). }
 assert(BPA:source_bounded M point(addM M count(succM M(succM M(zeroM M))))).
 { rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero. exact BP. }
 exists member,inner,namedpoint. refine(conj HM(conj HI(conj HN(conj HPoint _)))).
 exact(source_dn_representative_transport M count point carrier namedpoint named r(zeroM M)BPA HR HD HPoint HNamed).
Qed.
Print Assumptions source_carrier_point_reopen.
