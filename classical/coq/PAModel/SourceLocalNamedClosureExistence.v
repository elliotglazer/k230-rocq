(** A canonical actual closure-existence proof can be used at arbitrary
    model-valued carrier/successor/container/representative names, in its
    same closed axiom context. No new representation theorem is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes FixedSourceBounds
 SourceBounded NumericalContexts NumericalSourceFull NumericalContextRenaming SourceProofRenaming
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceFiniteParameters SourceFiniteNameParameters
 SourceRepresentationFalsityClosure SourceRepresentationClosureRecipe SourceEnvironmentCarrierClosure SourceDefinabilityPrimitives
 SourceLocalClosureWitnessRenaming SourceRoleReopening NumericalSubstitution SourceNamedQuantifierRules.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.
Theorem source_full_local_closed_renaming M b c n f rb rc rn delta g:
 context_bounded M b c n(zeroM M) ->source_full_prv M b c n f ->
 numerical_renaming M f rb rc rn delta g ->source_full_prv M b c n g.
Proof.
 intros HC HP HG. assert(HCtx:context_renaming M b c n rb rc rn delta b c).
 { intros i p q HI HP' HQ. assert(E:q=p)by(eapply beta_unique;eassumption). subst q.
   apply(numerical_renaming_identity_on_bound M p rb rc rn delta(zeroM M)(HC p(ex_intro _ i(conj HI HP')))).
   intros j HJ. exfalso. exact(coding_not_lt_zero M j HJ). }
 exact(source_full_prv_renaming M b c n f rb rc rn delta b c g HP HCtx HG).
Qed.
Definition local_closure_roles {A}(carrier successor container:A)i:=match i with 0=>carrier|1=>successor|_=>container end.
Theorem source_full_local_named_closure_exists M gb gc gn rep canonical carrier successor container witness
 openb openc assigned member body ex succ closure middle out:
 source_bounded M rep(code_numeral M 2) ->source_environment_carrier_closure_statement M rep canonical ->
 context_bounded M gb gc gn(zeroM M) ->source_full_prv M gb gc gn canonical ->
 witness<>carrier ->witness<>container ->source_role_reopening M carrier witness openb openc ->
 numerical_substitution M rep openb openc(code_numeral M 2)(code_numeral M 2)assigned ->
 sf_relation M SFMember witness container member ->sf_relation M SFAnd member assigned body ->
 source_named_quantifier M false witness body ex ->
 code_relation M(local_closure_roles carrier successor container)representation_successor_expression succ ->
 code_relation M(local_closure_roles carrier successor container)representation_closure_expression closure ->
 sf_relation M SFImpl closure ex middle ->sf_relation M SFImpl succ middle out ->
 source_full_prv M gb gc gn out.
Proof.
 intros BRep HCanonical HC PCanonical WA WC HOpen HAssigned HMember HBody HEx HS HCl HM HO.
 destruct(sf_relation_total M SFAnd(representation_member_code M)rep)as(cbody&HCB).
 destruct(sf_relation_total M SFEx cbody(zeroM M))as(cex&HCE).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode representation_closure_condition))cex)as(cmiddle&HCM).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode source_def_successor01))cmiddle)as(cout&HCO).
 pose proof(source_environment_carrier_closure_statement_join M rep cbody cex cmiddle cout HCB HCE HCM HCO)as HCout.
 assert(E:canonical=cout)by(eapply source_environment_carrier_closure_statement_functional;eassumption). subst cout.
 set(rho:=local_closure_roles carrier successor container).
 destruct(source_finite_names_total M 3 rho(zeroM M))as(rb&rc&HNames).
 assert(HAll:forall i x,code_relation M rho(source_finite_parameter_names 3 i)x ->
  renaming_lookup M rb rc(code_numeral M 3)(zeroM M)(code_numeral M i)x).
 { intros i x HX. unfold source_finite_parameter_names in HX. destruct(Nat.ltb_spec i 3)as[HI|HI].
   - change(x=rho i)in HX. subst x. exact(HNames i HI).
   - change(x=code_numeral M i)in HX. subst x.
     apply(proj2(renaming_lookup_outside M rb rc(code_numeral M 3)(zeroM M)(code_numeral M i)(code_numeral M i)
      ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M i 3))in H;lia))). symmetry;apply coding_add_zero_r. }
 pose proof(source_finite_parameter_renaming M source_def_successor01(source_finite_parameter_names 3)rho
  rb rc(code_numeral M 3)(zeroM M)succ HAll HS)as HSR.
 pose proof(source_finite_parameter_renaming M representation_closure_condition(source_finite_parameter_names 3)rho
  rb rc(code_numeral M 3)(zeroM M)closure HAll HCl)as HCR.
 pose proof(source_local_closure_witness_renaming M rep carrier container witness assigned rb rc(code_numeral M 3)
  openb openc member body ex cbody cex BRep WA WC HOpen HAssigned(HNames 0 ltac:(lia))(HNames 2 ltac:(lia))
  HMember HBody HEx HCB HCE)as HER.
 assert(HMR:numerical_renaming M cmiddle rb rc(code_numeral M 3)(zeroM M)middle).
 { apply(proj2(numerical_renaming_binary M SFImpl(code_numeral M(sf_encode representation_closure_condition))cex cmiddle
    rb rc(code_numeral M 3)(zeroM M)middle(or_intror(or_intror eq_refl))HCM)).
   exists closure,ex. auto. }
 assert(HOR:numerical_renaming M canonical rb rc(code_numeral M 3)(zeroM M)out).
 { apply(proj2(numerical_renaming_binary M SFImpl(code_numeral M(sf_encode source_def_successor01))cmiddle canonical
    rb rc(code_numeral M 3)(zeroM M)out(or_intror(or_intror eq_refl))HCO)).
   exists succ,middle. auto. }
 exact(source_full_local_closed_renaming M gb gc gn canonical rb rc(code_numeral M 3)(zeroM M)out HC PCanonical HOR).
Qed.
Print Assumptions source_full_local_closed_renaming.
Print Assumptions source_full_local_named_closure_exists.
