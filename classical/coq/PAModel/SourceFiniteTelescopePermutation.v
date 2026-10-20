(** Reordering a fixed finite proof macro uses actual source II and IE. *)
From PAModel Require Import Model SourceBounded SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_finite_telescope_inclusion M A B target old new k:
 (forall b,In b B ->source_bounded M b k) ->source_bounded M target k ->source_finite_telescope M A target old ->source_finite_telescope M B target new ->
 incl A B ->source_zfr_provable M old ->source_zfr_provable M new.
Proof.
 intros BB BT HO HN Included POld. apply(source_zfr_finite_rule M[old]B target new k BB BT HN).
 - intros x[<-|[]]. exact POld.
 - intros cb cc cn BC Laws Premises. apply(source_full_finite_telescope_apply M A target old HO cb cc cn).
   + apply Laws. now left.
   + intros a HA. apply Premises,Included. exact HA.
Qed.
Print Assumptions source_zfr_finite_telescope_inclusion.
