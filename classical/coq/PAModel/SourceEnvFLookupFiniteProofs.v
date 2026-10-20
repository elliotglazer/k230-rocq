(** Finite meta-level proof assembly with an internally numerical bound.
    Every leaf formula must have an actual source bound; the common bound
    is constructed by finite sums and imposes no restriction on model values. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SourceBounded SourceBoundMonotone
 SetFormulaCodes SetCodeDescent SourcePropositionalTemplates SourceEnvFLookupProofRules SourceWitnessProofComposition SourceZFRProvability.
From Stdlib Require Import Lists.List Lia Arith.Compare_dec.
Import ListNotations.
Unset Implicit Arguments.
Definition source_has_bound M f:=exists k,source_bounded M f k.
Theorem source_has_bound_binary_parts M h a b f:sf_binary h->sf_relation M h a b f->source_has_bound M f->
 source_has_bound M a/\source_has_bound M b.
Proof.
 intros HH HF(k&B). apply(proj1(source_bounded_accept_binary M h a b f k HH HF))in B.
 destruct B as(HA&HB). split;exists k;assumption.
Qed.
Theorem source_finite_common_bound M(codes:list(carrier M)):
 (forall f,In f codes->source_has_bound M f)->exists k,forall f,In f codes->source_bounded M f k.
Proof.
 induction codes as[|a codes IH];intro H.
 - exists(zeroM M). intros f HF. contradiction.
 - destruct(H a(or_introl eq_refl))as(k&HA).
   destruct(IH ltac:(intros f HF;exact(H f(or_intror HF))))as(l&HL).
   exists(addM M k l). intros f[<-|HF].
   + exact(source_bounded_monotone M a k(addM M k l)HA(coding_le_add M k l)).
   + apply(source_bounded_monotone M f l(addM M k l)(HL f HF)). rewrite add_comm. apply coding_le_add.
Qed.
Theorem source_zfr_prop_pairs_finite M(pairs:list(source_prop_template*carrier M))goal
 (program:source_prop_program(map fst pairs)goal)(codes:list(carrier M))result:
 (forall f,In f codes->source_has_bound M f)->
 (forall a f,In(a,f)pairs->code_relation M(fun i=>nth i codes(zeroM M))(source_prop_expression a)f/\source_zfr_provable M f)->
 code_relation M(fun i=>nth i codes(zeroM M))(source_prop_expression goal)result->source_zfr_provable M result.
Proof.
 intros HB HP HR. destruct(source_finite_common_bound M codes HB)as(k&HK).
 apply(source_zfr_prop_pairs M pairs goal program(fun i=>nth i codes(zeroM M))k result);[|exact HP|exact HR].
 intro i. destruct(lt_dec i(length codes))as[HI|HI].
 - apply HK,nth_In,HI.
 - rewrite nth_overflow by lia. apply source_bounded_accept_falsity.
Qed.
Print Assumptions source_finite_common_bound.
Print Assumptions source_zfr_prop_pairs_finite.
