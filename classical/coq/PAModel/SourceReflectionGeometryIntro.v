(** Actual finite source introduction of all eight reflection geometry facts. *)
From PAModel Require Import Model CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
 SourcePropositionalTemplates SourceReflectionGeometryPoint.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_full_reflection_geometry_intro M b c n m o kf u ob l mb s out bound:
 (forall i,source_bounded M(source_reflection_geometry_values m o kf u ob l mb s i)bound) ->context_bounded M b c n bound ->
 code_relation M(source_reflection_geometry_values m o kf u ob l mb s)(source_prop_expression source_reflection_geometry_payload)out ->
 source_full_prv M b c n m ->source_full_prv M b c n o ->source_full_prv M b c n kf ->source_full_prv M b c n u ->
 source_full_prv M b c n ob ->source_full_prv M b c n l ->source_full_prv M b c n mb ->source_full_prv M b c n s ->source_full_prv M b c n out.
Proof.
 intros Bounds BC HOut PM PO PKF PU POB PL PMB PS.
 apply(source_prop_program_sound M[SPTSlot 0;SPTSlot 1;SPTSlot 2;SPTSlot 3;SPTSlot 4;SPTSlot 5;SPTSlot 6;SPTSlot 7]
  source_reflection_geometry_payload source_reflection_geometry_payload_program(source_reflection_geometry_values m o kf u ob l mb s)bound b c n out Bounds BC);[|exact HOut].
 intros h HH f HF. destruct HH as[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
  cbn[source_prop_expression code_relation source_reflection_geometry_values]in HF;subst f;assumption.
Qed.
Print Assumptions source_full_reflection_geometry_intro.
