(** A source sequent's target assumptions: its relativized assumptions,
    followed by the internally finite table D(0),...,D(k-1). *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalEnvironments NumericalContexts NumericalContextRenaming
  ContextCombination ContextUnionRenaming SourceBounded SentenceBounds
  SourceRelativization SourceRelativizedContexts SourceRelativizedContextRenaming
  SourceDomainContexts.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_relative_context M domain b c n k u v l :=
  exists mb mc db dc,source_context_relativization M domain b c n mb mc /\
    source_domain_context M domain k db dc /\ context_union M mb mc n db dc k u v l.

Definition relative_context_lift4 (t : term) := t`[↑]`[↑]`[↑]`[↑].
Lemma relative_context_eval_lift4 M rho a b c d t :
  evalM M (a .: b .: c .: d .: rho) (relative_context_lift4 t)=evalM M rho t.
Proof. unfold relative_context_lift4,evalM. now rewrite !eval_up. Qed.

Definition source_relative_context_formula (domain b c n k u v l : term) : form :=
  ∃∃∃∃ (source_context_relativization_formula (relative_context_lift4 domain)
      (relative_context_lift4 b) (relative_context_lift4 c) (relative_context_lift4 n) $3 $2 ∧
    (source_domain_context_formula (relative_context_lift4 domain) (relative_context_lift4 k) $1 $0 ∧
    context_union_formula $3 $2 (relative_context_lift4 n) $1 $0
      (relative_context_lift4 k) (relative_context_lift4 u) (relative_context_lift4 v)
      (relative_context_lift4 l))).

Local Opaque holds source_context_relativization_formula source_domain_context_formula context_union_formula.
Theorem source_relative_context_formula_correct M rho domain b c n k u v l :
  holds M rho (source_relative_context_formula domain b c n k u v l) <->
  source_relative_context M (evalM M rho domain) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho u) (evalM M rho v) (evalM M rho l).
Proof.
  unfold source_relative_context_formula,source_relative_context.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_context_relativization_formula_correct.
  setoid_rewrite source_domain_context_formula_correct.
  setoid_rewrite context_union_formula_correct.
  setoid_rewrite relative_context_eval_lift4. reflexivity.
Qed.

Theorem source_relative_context_total M domain b c n k :
  exists u v l,source_relative_context M domain b c n k u v l.
Proof.
  destruct (source_context_relativization_total M domain b c n) as [mb [mc HM]].
  destruct (source_domain_context_total M domain k) as [db [dc HD]].
  destruct (context_union_total M mb mc n db dc k) as [u [v [l HU]]].
  exists u,v,l,mb,mc,db,dc. auto.
Qed.

Theorem source_relative_context_length M domain b c n k u v l :
  source_relative_context M domain b c n k u v l -> l=addM M n k.
Proof. intros [mb [mc [db [dc [_ [_ [EL _]]]]]]]. exact EL. Qed.

Theorem source_relative_context_member_iff M domain b c n k u v l f :
  source_relative_context M domain b c n k u v l ->
  (context_member M u v l f <->
    (exists g,context_member M b c n g /\ source_relativization M domain g f) \/
    (exists i,coding_lt M i k /\ NumericalInstantiation.numerical_instantiation M domain i f)).
Proof.
  intros [mb [mc [db [dc [HM [HD [_ HU]]]]]]]. rewrite HU.
  rewrite (source_context_relativization_member_iff M domain b c n mb mc f HM).
  rewrite (source_domain_context_member_iff M domain k db dc f HD). reflexivity.
Qed.

Theorem source_relative_context_bounded M domain b c n k u v l :
  source_bounded M domain (code_numeral M 1) -> context_bounded M b c n k ->
  source_relative_context M domain b c n k u v l -> context_bounded M u v l k.
Proof.
  intros HD HB [mb [mc [db [dc [HM [HDom [_ HU]]]]]]] f HF.
  apply HU in HF. destruct HF as [HF|HF].
  - exact (source_context_relativization_preserves_bound M domain b c n mb mc k HD HM HB f HF).
  - exact (source_domain_context_bounded M domain k db dc HD HDom f HF).
Qed.

Theorem source_relative_context_shift_cons M domain b c n k u v l
    bs cs us vs outb outc outn :
  source_bounded M domain (code_numeral M 1) ->
  source_relative_context M domain b c n k u v l ->
  context_shift M b c n bs cs -> context_shift M u v l us vs ->
  environment_cons M us vs l domain outb outc outn ->
  source_relative_context M domain bs cs n (succM M k) outb outc outn.
Proof.
  intros HD [mb [mc [db [dc [HM [HDC HU]]]]]] HS HUS HCons.
  destruct (context_shift_total M mb mc n) as [ms [mt HMS]].
  destruct (context_shift_total M db dc k) as [ds [dt HDS]].
  destruct (environment_cons_total M ds dt k domain) as [ds' [dt' [dk' HDCCons]]].
  pose proof (proj1 HDCCons) as EDK. subst dk'.
  exists ms,mt,ds',dt'. split.
  - exact (source_context_relativization_shift M domain b c n mb mc bs cs ms mt HD HM HS HMS).
  - split.
    + exact (source_domain_context_cons_shift M domain k db dc ds dt ds' dt'
        (succM M k) HD HDC HDS HDCCons).
    + apply (context_union_cons_right M ms mt n ds dt k us vs l domain
        ds' dt' (succM M k) outb outc outn);[|exact HDCCons|exact HCons].
      exact (context_union_renaming M mb mc n db dc k u v l
        (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M))
        ms mt ds dt us vs HU HMS HDS HUS).
Qed.

Theorem source_relative_context_formula_bound :
  bounded 8 (source_relative_context_formula $0 $1 $2 $3 $4 $5 $6 $7).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions source_relative_context_formula_correct.
Print Assumptions source_relative_context_total.
Print Assumptions source_relative_context_member_iff.
Print Assumptions source_relative_context_bounded.
Print Assumptions source_relative_context_shift_cons.

