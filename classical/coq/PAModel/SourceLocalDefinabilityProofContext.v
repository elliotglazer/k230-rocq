(** A single genuine closed ZFR context supports the varying matrix's
    representation theorem, its parameter EnvF existence, and every fixed
    Def/selection law. It is collected before choosing eigenvariables. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes NumericalSourceFull SourceBounded
 SourceRepresentationClosureRecipe SourceRepresentationUniform SourceEnvInClosureRecipe SourceEnvInClosureInduction
 SourceDefinabilityBounds SourceLocalDefinabilityContext SourceFiniteProofContexts SourceDescriptorProvability
 SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_local_definability_proof_context_total M count phi repClosure environment envClosure:
 source_bounded M phi(succM M count) ->source_representation_in_closure_recipe M(succM M count)phi repClosure ->
 source_envf M count environment ->source_env_in_closure_recipe M count environment envClosure ->
 exists b c n,source_local_fixed_context M b c n /\source_full_prv M b c n repClosure /\source_full_prv M b c n envClosure.
Proof.
 intros BF HR HE HC.
 set(fixed:=List.map(fun tag=>code_numeral M(sf_encode(source_local_fixed_formula tag)))(List.seq 0 7)).
 set(forms:=repClosure::envClosure::fixed).
 assert(HP:forall f,In f forms ->source_descriptor_provable M ZFRSourceDescriptor f).
 { intros f[<-|[<-|HF]].
   - apply(proj2(source_zfr_descriptor_provable M _)). exact(source_zfr_representation_uniform M phi(succM M count)repClosure BF HR).
   - apply(proj2(source_zfr_descriptor_provable M _)). exact(source_zfr_env_in_closure_uniform M count environment envClosure HE HC).
   - apply List.in_map_iff in HF. destruct HF as(tag&<-&HT). apply source_local_fixed_numeral_proof.
     apply List.in_seq in HT. lia. }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor forms HP)as(b&c&n&HCtx&P).
 exists b,c,n. split.
 - split;[exact(proj1(source_zfr_descriptor_context M b c n)HCtx)|]. intros tag HT. apply P.
   right;right. unfold fixed. apply List.in_map_iff. exists tag. split;[reflexivity|]. apply List.in_seq. lia.
 - split;apply P;[now left|right;now left].
Qed.
Print Assumptions source_local_definability_proof_context_total.
