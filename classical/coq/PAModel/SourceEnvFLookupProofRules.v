(** Compose a fixed finite list of actual ZFR deductions through a checked
    propositional program. Each supplied code is a genuine graph/proof pair. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SourceBoundMonotone SourcePropositionalTemplates
 SourceTraceBounds SourceFiniteProofContexts SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_prop_pairs M(pairs:list(source_prop_template*carrier M))goal(program:source_prop_program(map fst pairs)goal)rho k result:
 (forall i,source_bounded M(rho i)k)->
 (forall a f,In(a,f)pairs->code_relation M rho(source_prop_expression a)f/\source_zfr_provable M f)->
 code_relation M rho(source_prop_expression goal)result->source_zfr_provable M result.
Proof.
 intros HB HP HR.
 assert(Premises:forall f,In f(map snd pairs)->source_descriptor_provable M ZFRSourceDescriptor f).
 { intros f HF. apply in_map_iff in HF. destruct HF as(ag&E&HIn). destruct ag as[a g]. cbn in E. subst g.
   exact(proj2(source_zfr_descriptor_provable M f)(proj2(HP a f HIn))). }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor(map snd pairs)Premises)as(b&c&n&HC&P).
 exists b,c,n. split;[exact(proj1(source_zfr_descriptor_context M b c n)HC)|].
 apply(source_prop_program_sound M(map fst pairs)goal program rho k b c n result HB).
 - exact(context_bounded_monotone M b c n(zeroM M)k(proj1 HC)(coding_zero_lt_succ M k)).
 - intros a HA out HG. apply in_map_iff in HA. destruct HA as(af&E&HIn). destruct af as[a' f]. cbn in E. subst a'.
   pose proof(code_relation_functional M _ _ out f HG(proj1(HP a f HIn)))as EF. subst out.
   apply P. apply in_map_iff. exists(a,f). auto.
 - exact HR.
Qed.
Print Assumptions source_zfr_prop_pairs.


