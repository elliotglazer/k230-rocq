(** Symbolic evaluation of the exact364 native AX operations, before gate4947. *)
From PAModel Require Import CodeExpressions SearchStep Program230Configurations Program230AXSymbolic.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Inductive p230_ax_native_operation:=ANPush|ANLoad(n:nat)|ANCons|ANInc|ANUnpair|ANTransfer(source target:nat).
Definition p230_ax_native_program:list p230_ax_native_operation:=[ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANUnpair;ANTransfer 7 8;ANTransfer 6 5;ANPush;ANLoad 3;ANPush;ANUnpair;ANTransfer 7 8;ANTransfer 6 1;ANCons;ANPush;ANLoad 4;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 3;ANCons;ANPush;ANLoad 5;ANPush;ANLoad 3;ANCons;ANCons;ANCons;ANPush;ANLoad 3;ANPush;ANLoad 4;ANCons;ANInc;ANInc;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANInc;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANInc;ANCons;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 4;ANPush;ANLoad 3;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANPush;ANLoad 3;ANCons;ANPush;ANLoad 3;ANPush;ANLoad 4;ANCons;ANInc;ANInc;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 5;ANCons;ANInc;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANCons;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 5;ANPush;ANLoad 3;ANCons;ANInc;ANInc;ANCons;ANInc;ANInc;ANPush;ANLoad 5;ANPush;ANLoad 4;ANPush;ANLoad 3;ANCons;ANInc;ANInc;ANCons;ANInc;ANInc;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 4;ANCons;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 5;ANCons;ANInc;ANCons;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 5;ANPush;ANLoad 3;ANCons;ANCons;ANInc;ANInc;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANPush;ANLoad 4;ANPush;ANLoad 3;ANCons;ANInc;ANInc;ANCons;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANInc;ANPush;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANPush;ANLoad 3;ANPush;ANLoad 3;ANPush;ANLoad 5;ANPush;ANLoad 3;ANCons;ANInc;ANCons;ANPush;ANLoad 5;ANPush;ANLoad 5;ANPush;ANLoad 3;ANCons;ANInc;ANPush;ANLoad 4;ANPush;ANLoad 3;ANPush;ANLoad 4;ANPush;ANLoad 3;ANPush;ANLoad 3;ANPush;ANLoad 4;ANCons;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 5;ANCons;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANLoad 5;ANPush;ANLoad 3;ANPush;ANLoad 5;ANPush;ANLoad 3;ANPush;ANLoad 5;ANPush;ANLoad 3;ANCons;ANInc;ANPush;ANInc;ANCons;ANCons;ANPush;ANInc;ANCons;ANPush;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANCons;ANCons;ANInc;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANCons;ANPush;ANInc;ANCons;ANPush;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANCons;ANPush;ANInc;ANCons;ANPush;ANInc;ANCons;ANCons;ANInc;ANInc;ANPush;ANInc;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANCons;ANInc;ANInc;ANCons;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANInc;ANPush;ANLoad 3;ANPush;ANLoad 4;ANPush;ANLoad 5;ANCons;ANInc;ANInc;ANInc;ANCons;ANInc;ANInc;ANCons;ANPush;ANInc;ANCons;ANCons;ANPush;ANInc;ANCons;ANPush;ANInc;ANCons;ANCons;ANPush;ANInc;ANCons].
Definition p230_ax_native_add(x y:code_expr):code_expr:=
 match x,y with CEvar 1,CEvar 11=>CEvar 2|_,_=>p230_ax_add x y end.
Definition p230_ax_native_succ(x:code_expr):code_expr:=
 match x with CEconst n=>CEconst(S n)|CEadd b(CEconst n)=>CEadd b(CEconst(S n))|_=>CEadd x(CEconst 1)end.
Definition p230_ax_native_step(op:p230_ax_native_operation)(s:program230_configuration code_expr):option(program230_configuration code_expr):=
 match op with
 |ANPush=>Some(p230_ax_push s(CEconst 0))
 |ANLoad n=>match program230_register s 1 with CEconst 0=>Some(p230_ax_set s 1(program230_register s n))|_=>None end
 |ANCons=>p230_ax_binary E_wim s
 |ANInc=>Some(p230_ax_set s 1(p230_ax_native_succ(program230_register s 1)))
 |ANUnpair=>match program230_register s 8 with
  |CEvar 8=>Some(p230_ax_set(p230_ax_set(p230_ax_set s 8(CEconst 0))6(CEvar 11))7(CEvar 9))
  |CEvar 9=>Some(p230_ax_set(p230_ax_set(p230_ax_set s 8(CEconst 0))6(CEvar 4))7(CEvar 10))
  |_=>None end
 |ANTransfer a b=>Some(p230_ax_set(p230_ax_set s b(p230_ax_native_add(program230_register s b)(program230_register s a)))a(CEconst 0))
 end.
Fixpoint p230_ax_native_execute(ops:list p230_ax_native_operation)(s:program230_configuration code_expr):option(program230_configuration code_expr):=
 match ops with []=>Some s|op::tail=>match p230_ax_native_step op s with None=>None|Some s'=>p230_ax_native_execute tail s' end end.
Theorem p230_ax_native_normalization:
 p230_ax_native_execute p230_ax_native_program p230_ax_symbolic_initial=Some p230_ax_symbolic_final.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions p230_ax_native_normalization.
