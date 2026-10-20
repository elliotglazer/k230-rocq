(** Intermediate expression states for the literal native AX fold. *)
From PAModel Require Import CodeExpressions Program230Configurations Program230AXSymbolic Program230AXNativeSymbolic.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_native_row:Type:=(p230_ax_native_operation*program230_configuration code_expr*program230_configuration code_expr)%type.
Fixpoint p230_ax_native_trace(ops:list p230_ax_native_operation)(s:program230_configuration code_expr):option(list p230_ax_native_row):=
 match ops with
 |[]=>Some[]
 |op::tail=>match p230_ax_native_step op s with
  |None=>None
  |Some after=>match p230_ax_native_trace tail after with None=>None|Some rows=>Some((op,s,after)::rows)end
  end
 end.
Definition p230_ax_native_rows:=
 match p230_ax_native_trace p230_ax_native_program p230_ax_symbolic_initial with Some rows=>rows|None=>[]end.
Definition p230_ax_native_row_correct(row:p230_ax_native_row):Prop:=
 let '(op,before,after):=row in p230_ax_native_step op before=Some after.
Lemma p230_ax_native_trace_correct ops start rows:
 p230_ax_native_trace ops start=Some rows->Forall p230_ax_native_row_correct rows.
Proof.
 induction ops as[|op tail IH]in start,rows|-*;cbn[p230_ax_native_trace].
 -intro E;inversion E;constructor.
 -destruct(p230_ax_native_step op start)as[after|]eqn:HS;[|discriminate].
  destruct(p230_ax_native_trace tail after)as[rest|]eqn:HT;[|discriminate].
  intro E;inversion E;subst rows;constructor;[exact HS|exact(IH after rest HT)].
Qed.
Theorem p230_ax_native_rows_operations:
 map(fun row:p230_ax_native_row=>let '(op,_,_):=row in op)p230_ax_native_rows=p230_ax_native_program.
Proof. vm_compute;reflexivity. Qed.
Theorem p230_ax_native_rows_length:length p230_ax_native_rows=364.
Proof. vm_compute;reflexivity. Qed.
Theorem p230_ax_native_rows_correct:Forall p230_ax_native_row_correct p230_ax_native_rows.
Proof. apply(p230_ax_native_trace_correct p230_ax_native_program p230_ax_symbolic_initial);vm_compute;reflexivity. Qed.
Definition p230_ax_native_clean_row(row:p230_ax_native_row):Prop:=
 let '(op,before,_):=row in match op with ANTransfer _ _=>True|_=>
 program230_register before 6=CEconst 0 /\program230_register before 7=CEconst 0 end.
Definition p230_ax_native_clean_rowb(row:p230_ax_native_row):bool:=
 let '(op,before,_):=row in match op with ANTransfer _ _=>true|_=>
 match program230_register before 6,program230_register before 7 with CEconst 0,CEconst 0=>true|_,_=>false end end.
Lemma p230_ax_native_clean_rowb_sound row:
 p230_ax_native_clean_rowb row=true->p230_ax_native_clean_row row.
Proof.
 destruct row as[[op before]after];unfold p230_ax_native_clean_rowb,p230_ax_native_clean_row.
 destruct op as[|r| | | |a b];try (intros _;exact I);
 destruct(program230_register before 6)as[n|n|x y|x y|x y];try discriminate;
 destruct n;try discriminate;
 destruct(program230_register before 7)as[n|n|x y|x y|x y];try discriminate;
 destruct n;try discriminate;intros _;split;reflexivity.
Qed.
Theorem p230_ax_native_rows_clean:Forall p230_ax_native_clean_row p230_ax_native_rows.
Proof.
 assert(H:forallb p230_ax_native_clean_rowb p230_ax_native_rows=true)by(vm_compute;reflexivity).
 apply Forall_forall;intros row HI;apply p230_ax_native_clean_rowb_sound.
 exact(proj1(forallb_forall p230_ax_native_clean_rowb p230_ax_native_rows)H row HI).
Qed.
Theorem p230_ax_native_rows_final:
 snd(last p230_ax_native_rows(ANPush,p230_ax_symbolic_initial,p230_ax_symbolic_initial))=p230_ax_symbolic_final.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions p230_ax_native_trace_correct.
Print Assumptions p230_ax_native_rows_operations.
Print Assumptions p230_ax_native_rows_correct.
Print Assumptions p230_ax_native_rows_clean.
Print Assumptions p230_ax_native_rows_final.
