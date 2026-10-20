(** A beta-coded context supplies its own numerical bound on every formula
    it contains. Fresh names can therefore be chosen uniformly in any PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalEnvironments NumericalContexts
  CodeDescent FreshNames ContextualProofs BinaryMatrixRenaming TemplateNamedSubstitution.
Unset Implicit Arguments.

Theorem beta_entry_below_upper M b c i value upper :
  beta M b c i value -> coding_lt M b upper -> coding_lt M value upper.
Proof.
  intros [_ [d E]] [gap G].
  exists (addM M (mulM M d (beta_modulus M c i)) gap).
  rewrite G,E,(Arithmetic.add_comm M (mulM M d (beta_modulus M c i)) value),
    (Arithmetic.add_assoc M value (mulM M d (beta_modulus M c i)) gap).
  reflexivity.
Qed.

Theorem context_fresh_above_code M b c n name :
  coding_lt M b name -> context_fresh M b c n name.
Proof.
  intros H f [i [Hi Hb]]. apply (formula_above_is_fresh M f name).
  exact (beta_entry_below_upper M b c i f name Hb H).
Qed.

Theorem environment_avoids_above_code M b c n name :
  coding_lt M b name -> name<>zeroM M -> environment_avoids_name M b c n name.
Proof.
  intros H H0 i value [[Hi HB]|[Hi E]].
  - pose proof (beta_entry_below_upper M b c i value name HB H) as L.
    intro E;exact (template_lt_different M value name L (eq_sym E)).
  - subst value;congruence.
Qed.

Print Assumptions beta_entry_below_upper.
Print Assumptions context_fresh_above_code.
Print Assumptions environment_avoids_above_code.


Theorem environment_below_above_code M b c n bound :
  coding_lt M b bound -> coding_lt M (zeroM M) bound ->
  forall i value,environment_lookup M b c n i value -> coding_lt M value bound.
Proof.
  intros HB H0 i value [[Hi HV]|[Hi E]].
  - exact (beta_entry_below_upper M b c i value bound HV HB).
  - now subst value.
Qed.

Print Assumptions environment_below_above_code.
