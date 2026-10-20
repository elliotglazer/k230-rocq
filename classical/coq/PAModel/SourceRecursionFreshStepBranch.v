(** The genuine fresh-pair branch of an arbitrary-matrix attempt step. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourcePieceBoundMaxJoint SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionStructureBounds
 SourceRecursionSetOperations SourceRecursionSetOperationTransport SourceRecursionFreshPredecessorShell SourceRecursionBinaryInstance
 SourceRecursionAttemptStepShell SourceRecursionValuePairs SourceRecursionFreshPairWitness SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_fresh_step_branch M phi N z next f p q g u nextu v w inj mz sz appf adj mu su equalU equalV both binary target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M N k ->coding_lt M z k ->coding_lt M next k ->coding_lt M f k ->coding_lt M p k ->
 coding_lt M q k ->coding_lt M g k ->coding_lt M u k ->coding_lt M nextu k ->coding_lt M v k ->coding_lt M w k ->
 source_rec_injectivity M N inj ->sf_relation M SFMember z N mz ->source_rec_successor M z next sz ->source_rec_app M f z p appf ->
 source_rec_adjoin M f q g adj ->sf_relation M SFMember u N mu ->source_rec_successor M u nextu su ->sf_relation M SFEqual nextu next equalU ->
 sf_relation M SFEqual v w equalV ->sf_relation M SFAnd equalU equalV both ->source_rec_binary M phi p w binary ->source_rec_transition_witness M phi g u v target ->
 source_finite_telescope M[inj;mz;sz;appf;adj;mu;su;both;binary]target law ->source_zfr_provable M law.
Proof.
 intros BP BN BZ BNext BF BP' BQ BG BU BNextU BV BW HI HMZ HSZ HAF HA HMU HSU HEU HEV HB HG HT HLaw.
 destruct(source_zfr_rec_fresh_predecessor_total M N z next f p q g u nextu)
  as(inj'&mz'&sz'&appf'&adj'&mu'&su'&equal'&appg&structuralLaw&HI'&HMZ'&HSZ'&HAF'&HA'&HMU'&HSU'&HE'&HAG&HStructural&PStructural).
 pose proof(code_relation_functional M _ _ inj' inj HI' HI)as E. subst inj'.
 pose proof(sf_relation_functional M SFMember z N mz' mz HMZ' HMZ)as E. subst mz'.
 pose proof(code_relation_functional M _ _ sz' sz HSZ' HSZ)as E. subst sz'.
 pose proof(code_relation_functional M _ _ appf' appf HAF' HAF)as E. subst appf'.
 pose proof(code_relation_functional M _ _ adj' adj HA' HA)as E. subst adj'.
 pose proof(sf_relation_functional M SFMember u N mu' mu HMU' HMU)as E. subst mu'.
 pose proof(code_relation_functional M _ _ su' su HSU' HSU)as E. subst su'.
 pose proof(sf_relation_functional M SFEqual nextu next equal' equalU HE' HEU)as E. subst equal'.
 destruct(source_finite_telescope_total M[equalV;appg;binary]target)as(witnessLaw&HWitness).
 pose proof(source_zfr_rec_fresh_pair_witness M phi g u p v w equalV appg binary target witnessLaw k BP BG BU BP' BV BW HEV HAG HG HT HWitness)as PWitness.
 pose proof(source_rec_injectivity_bounded M N inj k BN HI)as BInj.
 assert(BMZ:source_bounded M mz k)by exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
 pose proof(source_rec_successor_bounded M z next sz k BZ BNext HSZ)as BSZ.
 pose proof(source_rec_app_bounded M f z p appf k BF BZ BP' HAF)as BAF.
 pose proof(source_rec_adjoin_bounded M f q g adj k BF BQ BG HA)as BAdj.
 assert(BMU:source_bounded M mu k)by exact(proj2(source_bounded_accept_atom M SFMember u N mu k(or_introl eq_refl)HMU)(conj BU BN)).
 pose proof(source_rec_successor_bounded M u nextu su k BU BNextU HSU)as BSU.
 assert(BEU:source_bounded M equalU k)by exact(proj2(source_bounded_accept_atom M SFEqual nextu next equalU k(or_intror eq_refl)HEU)(conj BNextU BNext)).
 assert(BEV:source_bounded M equalV k)by exact(proj2(source_bounded_accept_atom M SFEqual v w equalV k(or_intror eq_refl)HEV)(conj BV BW)).
 assert(BBoth:source_bounded M both k)by exact(proj2(source_bounded_accept_binary M SFAnd equalU equalV both k(or_introl eq_refl)HB)(conj BEU BEV)).
 pose proof(source_rec_binary_bounded M phi p w binary k BP BP' BW HG)as BGit.
 pose proof(source_rec_transition_witness_bounded M phi g u v target k BP BG BU BV HT)as BT.
 apply(source_zfr_finite_rule M[structuralLaw;witnessLaw][inj;mz;sz;appf;adj;mu;su;both;binary]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PI:source_full_prv M cb cc cn inj)by(apply Premises;cbn;tauto).
   assert(PMZ:source_full_prv M cb cc cn mz)by(apply Premises;cbn;tauto).
   assert(PSZ:source_full_prv M cb cc cn sz)by(apply Premises;cbn;tauto).
   assert(PAF:source_full_prv M cb cc cn appf)by(apply Premises;cbn;tauto).
   assert(PAdj:source_full_prv M cb cc cn adj)by(apply Premises;cbn;tauto).
   assert(PMU:source_full_prv M cb cc cn mu)by(apply Premises;cbn;tauto).
   assert(PSU:source_full_prv M cb cc cn su)by(apply Premises;cbn;tauto).
   assert(PBoth:source_full_prv M cb cc cn both)by(apply Premises;cbn;tauto).
   assert(PGit:source_full_prv M cb cc cn binary)by(apply Premises;cbn;tauto).
   destruct(source_full_piece_conjunction_components M cb cc cn equalU equalV both HB PBoth)as[PEU PEV].
   assert(PAppG:source_full_prv M cb cc cn appg).
   { apply(source_full_finite_telescope_apply M[inj;mz;sz;appf;adj;mu;su;equalU]appg structuralLaw HStructural cb cc cn).
     - apply Laws. now left.
     - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];assumption. }
   apply(source_full_finite_telescope_apply M[equalV;appg;binary]target witnessLaw HWitness cb cc cn).
   + apply Laws. right. now left.
   + intros x[<-|[<-|[<-|[]]]];assumption.
Qed.
Print Assumptions source_zfr_rec_fresh_step_branch.
