(** Container normalization includes the case where the generated name
    already is the prescribed name. No inverse substitution is assumed. *)
From PAModel Require Import Model Arithmetic CodeExpressions ProofTemplates
  NumericalProofs NamedLeibnizSteps TemplatePropositional TemplateFormulaFresh
  QuotedSameContainer RawSelectionAlpha.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem numerical_raw_selection_exists_normalize M rho T A K C W Theta tv av kv cv wv :
  code_relation M rho T tv -> code_relation M rho A av ->
  code_relation M rho K kv -> code_relation M rho C cv -> code_relation M rho W wv ->
  kv<>zeroM M -> cv<>zeroM M ->
  tv<>kv -> av<>kv -> wv<>kv -> tv<>cv -> av<>cv -> wv<>cv ->
  expression_fresh M rho kv Theta -> expression_fresh M rho cv Theta ->
  ns_proof M rho
    (E_wim (E_wex K (E_raw_selection_container T A K W Theta))
      (E_wex C (E_raw_selection_container T A C W Theta))).
Proof.
  intros HT HA HK HC HW HK0 HC0 HTK HAK HWK HTC HAC HWC HFk HFc.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H r=>axioms M ax r H) kv cv) as [E|HNe].
  - subst cv. destruct (code_relation_total M Theta rho) as [theta HTheta].
    set (body:=fun Binder=>E_wex Binder
      (E_raw_selection_container (CEvar 2) (CEvar 3) Binder (CEvar 4) (CEvar 5))).
    set (e:=E_wim (body (CEvar 0)) (body (CEvar 1))).
    set (s1:=fun idx : nat => match idx with 0=>K|1=>C|2=>T|3=>A|4=>W|5=>Theta|_=>CEconst 0 end).
    set (s2:=fun idx : nat => match idx with 0=>K|1=>K|2=>T|3=>A|4=>W|5=>Theta|_=>CEconst 0 end).
    set (values:=fun idx : nat => match idx with 0=>kv|1=>kv|2=>tv|3=>av|4=>wv|5=>theta|_=>zeroM M end).
    assert (HS1:forall idx,code_relation M rho (s1 idx) (values idx)).
    { intros [|[|[|[|[|[|i]]]]]];assumption||reflexivity. }
    assert (HS2:forall idx,code_relation M rho (s2 idx) (values idx)).
    { intros [|[|[|[|[|[|i]]]]]];assumption||reflexivity. }
    intros result HResult.
    change (code_relation M rho (code_subst s1 e) result) in HResult.
    apply (proj1 (code_subst_graph M rho s1 values HS1 e result)) in HResult.
    apply (proj2 (code_subst_graph M rho s2 values HS2 e result)) in HResult.
    change (code_relation M rho
      (E_wim (E_wex K (E_raw_selection_container T A K W Theta))
        (E_wex K (E_raw_selection_container T A K W Theta))) result) in HResult.
    exact (ns_proof_template M rho _ (template_I nil _) result HResult).
  - exact (numerical_raw_selection_exists_alpha M rho T A K C W Theta tv av kv cv wv
      HT HA HK HC HW HK0 HC0 HNe HTK HAK HWK HTC HAC HWC HFk HFc).
Qed.

Print Assumptions numerical_raw_selection_exists_normalize.
