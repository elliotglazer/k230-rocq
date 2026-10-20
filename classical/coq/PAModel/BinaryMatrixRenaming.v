(** Capture-safe renaming of either free argument of an actual source
    matrix. Destination names may lie above the original binder name. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalEnvironments
  NamedSubstitutionRules NamedSubstitution QuotationNamedSubstitution NumericalQuotation
  QuotationFunctionality ReplacementMatrixQuotation.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition environment_avoids_name M b c n name :=
  forall i v,environment_lookup M b c n i v -> v<>name.

Lemma environment_avoids_name_cons M b c n d e m value name :
  environment_avoids_name M b c n name -> value<>name ->
  environment_cons M b c n value d e m -> environment_avoids_name M d e m name.
Proof.
  intros HA Hvalue HC i v HV.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M b c n value d e m v HC)) in HV;now subst v.
  - exact (HA j v (proj1 (environment_cons_tail M b c n value d e m j v HC) HV)).
Qed.

Lemma environment_head_replacement_avoiding M b c n d e m f g l old new :
  environment_avoids_name M b c n old ->
  environment_cons M b c n old d e m -> environment_cons M b c n new f g l ->
  environment_named_replace M d e m f g l old new.
Proof.
  intros HA HD HF i v w HV HW.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M b c n old d e m v HD)) in HV.
    apply (proj1 (environment_cons_head M b c n new f g l w HF)) in HW.
    subst v w;left;auto.
  - apply (proj1 (environment_cons_tail M b c n old d e m j v HD)) in HV.
    apply (proj1 (environment_cons_tail M b c n new f g l j w HF)) in HW.
    assert (E:v=w) by exact (environment_lookup_functional M b c n j v w HV HW).
    subst w;right;split;[exact (HA j v HV)|reflexivity].
Qed.

Theorem binary_matrix_input_rename M phi eb ec en old new output fresh domain f g :
  old<>zeroM M -> domain<>old -> output<>old ->
  coding_lt M old fresh -> coding_lt M new fresh -> environment_avoids_name M eb ec en old ->
  binary_matrix_quotation M phi eb ec en old output fresh domain f ->
  binary_matrix_quotation M phi eb ec en new output fresh domain g ->
  named_substitution M f old new g.
Proof.
  intros H0 HT HO HF HN HA [ob [oc [on [fb [fc [fn [CO [CF HQF]]]]]]]] HQG.
  destruct (environment_cons_total M ob oc on new) as [gb [gc [gn CG]]].
  destruct (numerical_quotation_total M phi gb gc gn fresh domain) as [q HQ].
  assert (E:q=g).
  { apply (binary_matrix_quotation_functional M phi eb ec en new output fresh domain q g);[|exact HQG].
    exists ob,oc,on,gb,gc,gn;split;[exact CO|]. split;assumption. }
  subst q.
  exact (numerical_quotation_named_substitution M phi fb fc fn gb gc gn fresh domain old new f g
    H0 HT HF HN (environment_head_replacement_avoiding M ob oc on fb fc fn gb gc gn old new
      (environment_avoids_name_cons M eb ec en ob oc on output old HA HO CO) CF CG) HQF HQ).
Qed.

Theorem binary_matrix_output_rename M phi eb ec en input old new fresh domain f g :
  old<>zeroM M -> domain<>old -> input<>old ->
  coding_lt M old fresh -> coding_lt M new fresh -> environment_avoids_name M eb ec en old ->
  binary_matrix_quotation M phi eb ec en input old fresh domain f ->
  binary_matrix_quotation M phi eb ec en input new fresh domain g ->
  named_substitution M f old new g.
Proof.
  intros H0 HT HI HF HN HA [ob [oc [on [fb [fc [fn [CO [CF HQF]]]]]]]] HQG.
  destruct (environment_cons_total M eb ec en new) as [nb [nc [nn CN]]].
  destruct (environment_cons_total M nb nc nn input) as [gb [gc [gn CG]]].
  destruct (numerical_quotation_total M phi gb gc gn fresh domain) as [q HQ].
  assert (E:q=g).
  { apply (binary_matrix_quotation_functional M phi eb ec en input new fresh domain q g);[|exact HQG].
    exists nb,nc,nn,gb,gc,gn;split;[exact CN|]. split;assumption. }
  subst q.
  exact (numerical_quotation_named_substitution M phi fb fc fn gb gc gn fresh domain old new f g
    H0 HT HF HN (environment_named_replace_cons M ob oc on nb nc nn fb fc fn gb gc gn old new input
      (environment_head_replacement_avoiding M eb ec en ob oc on nb nc nn old new HA CO CN)
      HI CF CG) HQF HQ).
Qed.

Print Assumptions binary_matrix_input_rename.
Print Assumptions binary_matrix_output_rename.
