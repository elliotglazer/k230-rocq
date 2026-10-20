(** Remove a proved ZFR theorem from the tail of a finite macro by
    actual source implication elimination and introduction. *)
From PAModel Require Import Model SourceBounded SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_finite_telescope_remove_theorem M A proved target old new k:
 (forall a,In a A ->source_bounded M a k) ->source_bounded M target k ->
 source_finite_telescope M(A++[proved])target old ->source_finite_telescope M A target new ->
 source_zfr_provable M proved ->source_zfr_provable M old ->source_zfr_provable M new.
Proof.
 intros BA BT HO HN PProved POld.
 apply(source_zfr_finite_rule M[old;proved]A target new k BA BT HN).
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   apply(source_full_finite_telescope_apply M(A++[proved])target old HO cb cc cn).
   + apply Laws. now left.
   + intros a HA. apply in_app_iff in HA. destruct HA as[HA|[<-|[]]].
     * exact(Premises a HA).
     * apply Laws. right. now left.
Qed.
Print Assumptions source_zfr_finite_telescope_remove_theorem.
