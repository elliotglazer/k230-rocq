(** The literal public AX action has no remaining compiler premise. *)
From PAModel Require Import Model Program230AXContract Program230AXPublicFold
 Program230AXRowRuntime Program230AXActionAssembly.
Unset Implicit Arguments.
Theorem p230_actual_ax_action M:p230_ax_action_contract M.
Proof.
 apply p230_ax_action_from_public_rows;intros env HE HP0 HP1 item op before after HI start HPC HG.
 exact(p230_ax_actual_typed_row M env item op before after HE HP0 HP1 HI start HPC HG).
Qed.
Print Assumptions p230_actual_ax_action.
