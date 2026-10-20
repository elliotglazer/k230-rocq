(** Actual uniform An-in-C existence, proved by PA-definable induction
    over the arbitrary model-valued assignment length. *)
From PAModel Require Import Model NumericalProofs CodeExpressions SourceEnvironmentCarrierRecipe
 SourceEnvironmentCarrierClosure SourceEnvironmentCarrierBase SourceEnvironmentCarrierStep SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_environment_carrier_uniform M:forall count,source_environment_carrier_proof_at M count.
Proof.
 apply(definable_induction M(source_environment_carrier_proof_at M)(source_environment_carrier_proof_definable M)).
 - intros carrier out HR HO. exact(source_zfr_environment_carrier_zero M carrier out HR HO).
 - intros count IH. exact(source_zfr_environment_carrier_step M count IH).
Qed.
Theorem source_zfr_environment_carrier_total M count:exists carrier out,
 source_environment_carrier_recipe M count carrier /\source_environment_carrier_closure_statement M carrier out /\
 source_zfr_provable M out.
Proof.
 destruct(source_environment_carrier_recipe_total M count)as(carrier&HR).
 destruct(source_environment_carrier_closure_statement_total M carrier)as(out&HO).
 exists carrier,out. exact(conj HR(conj HO(source_zfr_environment_carrier_uniform M count carrier out HR HO))).
Qed.
Print Assumptions source_zfr_environment_carrier_uniform.
Print Assumptions source_zfr_environment_carrier_total.
