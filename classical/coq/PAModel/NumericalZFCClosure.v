(** The final closedness check in the schema recognizer is redundant.
    This holds for arbitrary PA-model codes and closure lengths, not only
    encodings of external finite formulas. *)
From PAModel Require Import Model SourceBounded SourceBoundedCalibration
  SchemaRenamingBounds SchemaConstructorBounds NumericalZFCAxioms.
Unset Implicit Arguments.

Theorem numerical_separation_instance_closed M phi n z :
  numerical_separation_instance M phi n z -> source_bounded M z (zeroM M).
Proof.
  intros [Hphi [body [open_code [Hr [Ho Hz]]]]].
  apply (all_prefix_closes M n open_code z); [|exact Hz].
  apply (schema_separation_constructor_bound M body open_code n); [|exact Ho].
  exact (schema_separation_bound M phi body n Hphi Hr).
Qed.

Theorem numerical_replacement_instance_closed M phi n z :
  numerical_replacement_instance M phi n z -> source_bounded M z (zeroM M).
Proof.
  intros [Hphi [a [b [c [open_code [Ha [Hb [Hc [Ho Hz]]]]]]]]].
  apply (all_prefix_closes M n open_code z); [|exact Hz].
  apply (schema_replacement_constructor_bound M a b c open_code n); [| | |exact Ho].
  - exact (schema_replacement_a_bound M phi a n Hphi Ha).
  - exact (schema_replacement_b_bound M phi b n Hphi Hb).
  - exact (schema_replacement_c_bound M phi c n Hphi Hc).
Qed.

Theorem numerical_closed_separation_redundant M z :
  numerical_closed_separation M z <-> exists phi n, numerical_separation_instance M phi n z.
Proof.
  split; [intros [_ H];exact H|].
  intros [phi [n H]]. split.
  - exact (numerical_separation_instance_closed M phi n z H).
  - now exists phi,n.
Qed.

Theorem numerical_closed_replacement_redundant M z :
  numerical_closed_replacement M z <-> exists phi n, numerical_replacement_instance M phi n z.
Proof.
  split; [intros [_ H];exact H|].
  intros [phi [n H]]. split.
  - exact (numerical_replacement_instance_closed M phi n z H).
  - now exists phi,n.
Qed.

Theorem numerical_separation_closed_total M phi n :
  source_bounded M phi (succM M n) ->
  exists z, numerical_separation_instance M phi n z /\ numerical_closed_separation M z.
Proof.
  intro Hphi. destruct (numerical_separation_instance_total M phi n Hphi) as [z Hz].
  exists z. split; [exact Hz|]. apply numerical_closed_separation_redundant.
  now exists phi,n.
Qed.

Theorem numerical_replacement_closed_total M phi n :
  source_bounded M phi (succM M (succM M n)) ->
  exists z, numerical_replacement_instance M phi n z /\ numerical_closed_replacement M z.
Proof.
  intro Hphi. destruct (numerical_replacement_instance_total M phi n Hphi) as [z Hz].
  exists z. split; [exact Hz|]. apply numerical_closed_replacement_redundant.
  now exists phi,n.
Qed.

Corollary numerical_separation_axiom_total M phi n :
  source_bounded M phi (succM M n) ->
  exists z, numerical_separation_instance M phi n z /\ numerical_zfc_source_axiom M z.
Proof.
  intro H. destruct (numerical_separation_closed_total M phi n H) as [z [Hz Hclosed]].
  exists z. split; [exact Hz|right;left;exact Hclosed].
Qed.

Corollary numerical_replacement_axiom_total M phi n :
  source_bounded M phi (succM M (succM M n)) ->
  exists z, numerical_replacement_instance M phi n z /\ numerical_zfc_source_axiom M z.
Proof.
  intro H. destruct (numerical_replacement_closed_total M phi n H) as [z [Hz Hclosed]].
  exists z. split; [exact Hz|right;right;exact Hclosed].
Qed.
