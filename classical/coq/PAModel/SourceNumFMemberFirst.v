(** Reorder a genuine numeral-in-closure witness using actual source
    existential elimination and introduction. The matrix is arbitrary. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceInstantiationConstructors SourceSequents SourceTraceBounds
 NumericalContexts NumericalEnvironments NumericalSourceFull SourceContextTransport SourceContextProofHelpers
 SourceUpperProofHelpers SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability
 SourceNumFClosureRecipe SourceDefinabilityPrimitives SourceEnvironmentCarrierClosure SourceRepresentationFalsityClosure SourceRepresentationClosureRecipe.
Unset Implicit Arguments.
Lemma source_full_atomic_apply M b c n a d f:
 sf_relation M SFImpl a d f->source_full_prv M b c n f->source_full_prv M b c n a->source_full_prv M b c n d.
Proof.
 intros H P Q. apply(full_source_IE M b c n a d f);try assumption.
 exact(source_wf_binary_right M b c n SFImpl a d f(or_intror(or_intror eq_refl))H(source_full_prv_wellformed M b c n f P)).
Qed.
Theorem source_zfr_double_exists_swap M s c a d pair swapped ex oldex middle whole next result:
 sf_relation M SFAnd a d pair->sf_relation M SFAnd d a swapped->
 sf_relation M SFEx pair(zeroM M)ex->sf_relation M SFEx swapped(zeroM M)oldex->
 sf_relation M SFImpl c ex middle->sf_relation M SFImpl s middle whole->
 sf_relation M SFImpl c oldex next->sf_relation M SFImpl s next result->
 source_zfr_provable M whole->source_zfr_provable M result.
Proof.
 intros HP HS HE HO HM HW HN HR(b&cb&n&HZ&PWhole).
 destruct(source_full_prv_wellformed M b cb n whole PWhole)as(k&BWhole&BCtx).
 destruct(proj1(source_bounded_accept_binary M SFImpl s middle whole k(or_intror(or_intror eq_refl))HW)BWhole)as(BS&BMiddle).
 destruct(proj1(source_bounded_accept_binary M SFImpl c ex middle k(or_intror(or_intror eq_refl))HM)BMiddle)as(BC&BEx).
 destruct(environment_cons_total M b cb n s)as(u&v&l&HConsS).
 assert(BSCtx:context_bounded M u v l k)by(exact(proj2(context_bounded_cons M b cb n s u v l k HConsS)(conj BS BCtx))).
 pose proof(source_full_cons_head M b cb n s u v l k HConsS BS BSCtx)as PS.
 pose proof(source_full_cons_weaken M b cb n s u v l k whole HConsS BSCtx PWhole)as PW.
 destruct(environment_cons_total M u v l c)as(p&q&r&HConsC).
 assert(BCCtx:context_bounded M p q r k)by(exact(proj2(context_bounded_cons M u v l c p q r k HConsC)(conj BC BSCtx))).
 pose proof(source_full_cons_head M u v l c p q r k HConsC BC BCCtx)as PC.
 pose proof(source_full_cons_weaken M u v l c p q r k s HConsC BCCtx PS)as PS'.
 pose proof(source_full_cons_weaken M u v l c p q r k whole HConsC BCCtx PW)as PW'.
 pose proof(source_full_atomic_apply M p q r s middle whole HW PW' PS')as PM.
 pose proof(source_full_atomic_apply M p q r c ex middle HM PM PC)as PE.
 pose proof(source_full_exists_conjunction_swap M p q r a d pair swapped ex oldex HP HS HE HO PE)as PN.
 pose proof(source_full_implication_intro M u v l c oldex next p q r HConsC HN PN)as PNext.
 exists b,cb,n. split;[exact HZ|].
 exact(source_full_implication_intro M b cb n s next result u v l HConsS HR PNext).
Qed.
Theorem source_zfr_numf_member_first M matrix old result:
 source_numf_closure_statement M matrix old->source_environment_carrier_closure_statement M matrix result->
 source_zfr_provable M old->source_zfr_provable M result.
Proof.
 intros HOld HResult POld.
 destruct(source_numf_closure_statement_parts M matrix old HOld)as(pair&ex&middle&(HP&HE)&HM&HW).
 destruct(sf_relation_total M SFAnd(representation_member_code M)matrix)as(swapped&HS).
 destruct(sf_relation_total M SFEx swapped(zeroM M))as(oldex&HO).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode representation_closure_condition))oldex)as(next&HN).
 destruct(sf_relation_total M SFImpl(code_numeral M(sf_encode source_def_successor01))next)as(result'&HR).
 pose proof(source_environment_carrier_closure_statement_join M matrix swapped oldex next result' HS HO HN HR)as HJoin.
 rewrite(source_environment_carrier_closure_statement_functional M matrix result result' HResult HJoin).
 exact(source_zfr_double_exists_swap M _ _ matrix(representation_member_code M)pair swapped ex oldex middle old next result'
   HP HS HE HO HM HW HN HR POld).
Qed.
Print Assumptions source_zfr_double_exists_swap.
Print Assumptions source_zfr_numf_member_first.
