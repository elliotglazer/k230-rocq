(** The full old/fresh value-case argument for an arbitrary internal step matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceDerivedRules
 SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceFiniteTelescopePermutation SourceZFRFiniteRule SourcePropositionalCases
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionStructureGraphs SourceRecursionStructureBounds
 SourceRecursionSetOperations SourceRecursionSetOperationTransport SourceRecursionAdjoinCases SourceRecursionBinaryInstance SourceRecursionAttemptStepShell
 SourceRecursionValuePairs SourceRecursionFreshStepBranch SourceRecursionOldStepBranch SourceParameterGraphs SourceFiniteNameParameters SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma source_rec_ordered_pair_bounded M x y q out k:
 coding_lt M x k ->coding_lt M y k ->coding_lt M q k ->source_rec_ordered_pair M x y q out ->source_bounded M out k.
Proof.
 intros BX BY BQ HO. apply(source_parameter_graph_bounded M 3 source_rec_ordered_pair_predicate source_rec_ordered_pair_finite_bound
  (source_finite_parameter_names 3)(source_rec_env3 x y q)k);[|exact HO].
 intros[|[|[|i]]]a HI HX;try lia.
 - change(a=x)in HX. now subst a.
 - change(a=y)in HX. now subst a.
 - change(a=q)in HX. now subst a.
Qed.
Theorem source_zfr_rec_extension_point M phi o a N f q g z next p w u nextu v inj att mz sz appf adj op binary mu su appg target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->coding_lt M u k ->coding_lt M nextu k ->coding_lt M v k ->
 source_rec_injectivity M N inj ->source_rec_attempt M phi o a N f att ->sf_relation M SFMember z N mz ->source_rec_successor M z next sz ->
 source_rec_app M f z p appf ->source_rec_adjoin M f q g adj ->source_rec_ordered_pair M next w q op ->source_rec_binary M phi p w binary ->
 sf_relation M SFMember u N mu ->source_rec_successor M u nextu su ->source_rec_app M g nextu v appg ->source_rec_transition_witness M phi g u v target ->
 source_finite_telescope M[inj;att;mz;sz;appf;adj;op;binary;mu;su;appg]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BQ BG BZ BNext BP' BW BU BNextU BV HI HAtt HMZ HSZ HAppF HA HOp HBinary HMU HSU HAppG HT HLaw.
 destruct(source_zfr_rec_adjoin_cases_total M f q g next w nextu v)
  as(adj'&op'&appg'&oldApp&eqU&eqV&both&cases&t2&t1&casesLaw&HA'&HOp'&HAppG'&HOldApp&HEU&HEV&HBoth&HCases&H3&H2&H1&PCasesLaw).
 pose proof(code_relation_functional M _ _ adj' adj HA' HA)as E. subst adj'.
 pose proof(code_relation_functional M _ _ op' op HOp' HOp)as E. subst op'.
 pose proof(code_relation_functional M _ _ appg' appg HAppG' HAppG)as E. subst appg'.
 pose proof(source_rec_injectivity_bounded M N inj k BN HI)as BInj.
 pose proof(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HAtt)as BAtt.
 assert(BMZ:source_bounded M mz k)by exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
 pose proof(source_rec_successor_bounded M z next sz k BZ BNext HSZ)as BSZ.
 pose proof(source_rec_app_bounded M f z p appf k BF BZ BP' HAppF)as BAppF.
 pose proof(source_rec_adjoin_bounded M f q g adj k BF BQ BG HA)as BAdj.
 pose proof(source_rec_ordered_pair_bounded M next w q op k BNext BW BQ HOp)as BOp.
 pose proof(source_rec_binary_bounded M phi p w binary k BP BP' BW HBinary)as BGit.
 assert(BMU:source_bounded M mu k)by exact(proj2(source_bounded_accept_atom M SFMember u N mu k(or_introl eq_refl)HMU)(conj BU BN)).
 pose proof(source_rec_successor_bounded M u nextu su k BU BNextU HSU)as BSU.
 pose proof(source_rec_app_bounded M g nextu v appg k BG BNextU BV HAppG)as BAppG.
 pose proof(source_rec_transition_witness_bounded M phi g u v target k BP BG BU BV HT)as BT.
 pose proof(source_rec_app_bounded M f nextu v oldApp k BF BNextU BV HOldApp)as BOldApp.
 assert(BEU:source_bounded M eqU k)by exact(proj2(source_bounded_accept_atom M SFEqual nextu next eqU k(or_intror eq_refl)HEU)(conj BNextU BNext)).
 assert(BEV:source_bounded M eqV k)by exact(proj2(source_bounded_accept_atom M SFEqual v w eqV k(or_intror eq_refl)HEV)(conj BV BW)).
 assert(BBoth:source_bounded M both k)by exact(proj2(source_bounded_accept_binary M SFAnd eqU eqV both k(or_introl eq_refl)HBoth)(conj BEU BEV)).
 destruct(sf_relation_total M SFImpl oldApp target)as(oldImp&HOldImp).
 destruct(source_finite_telescope_total M[att;mu;su;adj]oldImp)as(oldLaw&HOldPrefix).
 assert(HOldFull:source_finite_telescope M[att;mu;su;adj;oldApp]target oldLaw).
 { apply(source_finite_telescope_prefix M[att;mu;su;adj][oldApp]oldImp target oldLaw HOldPrefix). exists target. split;[reflexivity|exact HOldImp]. }
 pose proof(source_zfr_rec_old_step_branch M phi o a N f q g u nextu v att mu su adj oldApp target oldLaw k
  BP BO BA BN BF BQ BG BU BNextU BV HAtt HMU HSU HA HOldApp HT HOldFull)as POldLaw.
 destruct(sf_relation_total M SFImpl both target)as(freshImp&HFreshImp).
 destruct(source_finite_telescope_total M[inj;mz;sz;appf;adj;mu;su;binary]freshImp)as(freshLaw&HFreshPrefix).
 assert(HFreshFull:source_finite_telescope M[inj;mz;sz;appf;adj;mu;su;binary;both]target freshLaw).
 { apply(source_finite_telescope_prefix M[inj;mz;sz;appf;adj;mu;su;binary][both]freshImp target freshLaw HFreshPrefix). exists target. split;[reflexivity|exact HFreshImp]. }
 destruct(source_finite_telescope_total M[inj;mz;sz;appf;adj;mu;su;both;binary]target)as(originalFreshLaw&HOriginalFresh).
 pose proof(source_zfr_rec_fresh_step_branch M phi N z next f p q g u nextu v w inj mz sz appf adj mu su eqU eqV both binary target originalFreshLaw k
  BP BN BZ BNext BF BP' BQ BG BU BNextU BV BW HI HMZ HSZ HAppF HA HMU HSU HEU HEV HBoth HBinary HT HOriginalFresh)as POriginalFresh.
 assert(PFreshLaw:source_zfr_provable M freshLaw).
 { apply(source_zfr_finite_telescope_inclusion M[inj;mz;sz;appf;adj;mu;su;both;binary][inj;mz;sz;appf;adj;mu;su;binary;both]target originalFreshLaw freshLaw k).
   - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];assumption.
   - exact BT.
   - exact HOriginalFresh.
   - exact HFreshFull.
   - intros x HX. cbn in *. tauto.
   - exact POriginalFresh. }
 apply(source_zfr_finite_rule M[casesLaw;oldLaw;freshLaw][inj;att;mz;sz;appf;adj;op;binary;mu;su;appg]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros x[<-|[<-|[<-|[]]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PCases:source_full_prv M cb cc cn cases).
   { pose proof(source_full_modus_ponens M cb cc cn adj t1 casesLaw H1(Laws casesLaw(or_introl eq_refl))(Premises adj ltac:(cbn;tauto)))as P1.
     pose proof(source_full_modus_ponens M cb cc cn op t2 t1 H2 P1(Premises op ltac:(cbn;tauto)))as P2.
     exact(source_full_modus_ponens M cb cc cn appg cases t2 H3 P2(Premises appg ltac:(cbn;tauto))). }
   assert(POld:source_full_prv M cb cc cn oldImp).
   { apply(source_full_finite_telescope_apply M[att;mu;su;adj]oldImp oldLaw HOldPrefix cb cc cn).
     - apply Laws. right. now left.
     - intros x HX. apply Premises. cbn in *. tauto. }
   assert(PFresh:source_full_prv M cb cc cn freshImp).
   { apply(source_full_finite_telescope_apply M[inj;mz;sz;appf;adj;mu;su;binary]freshImp freshLaw HFreshPrefix cb cc cn).
     - apply Laws. right. right. now left.
     - intros x HX. apply Premises. cbn in *. tauto. }
   exact(source_full_cases M cb cc cn oldApp both target cases oldImp freshImp k BOldApp BBoth BT BC HCases HOldImp HFreshImp PCases POld PFresh).
Qed.
Print Assumptions source_rec_ordered_pair_bounded.
Print Assumptions source_zfr_rec_extension_point.
