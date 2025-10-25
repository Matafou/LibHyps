(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

From Stdlib Require Import Arith ZArith List.
Require LibHyps.TacNewHyps.
Import TacNewHyps.Notations.
(* Import ListNotations. *)
(* Local Open Scope list. *)
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
Local Set Default Proof Mode "Classic".
Require Import LibHyps.LibHypsDebug.

Local Ltac2 backtrack (msg:string) := Control.zero (Tactic_failure (Some (fprintf "Backtrack: %s" msg))).
Local Ltac2 control_try tac := Control.plus tac (fun _ => ()). 
(** This file defines a tactic "autorename h" (and "autorename_strict
    h") that automatically rename hypothesis h followinh a systematic,
    but customizable heuristic.

    Comments welcome. *)

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
From Stdlib Require Import ZArith.

(** ** The custom renaming tactic

  The tactic "rename_hyp" should be redefined along a coq development,
  it should return a fresh name build from a type th and a depth. It
  should fail if no name is found, so that the fallback scheme is
  called.

  Typical use, in increasing order of complexity, approximatively
  equivalent to the decreasing order of interest.

<<
Ltac rename_hyp1 n th :=
  match th with
  | List.In ?e ?l => name ( `_lst_in` ++ e#n ++ l#O)
  | InA _ ?e ?l => name( `_inA` ++ e#n ++ l#0)
  | @StronglySorted _ ?ord ?l => name ( `_strgSorted` ++ l#(S (S n)))
  | @Forall _ ?P ?x => name (`_lst_forall` ++ P#n ++ x#n)
  | @Forall2 _ _ ?P ?x ?y => name (`_lst_forall2` ++ P#n ++ x#n ++ y#n)
  | NoDupA _ ?l => name (`_NoDupA` ++ l#n)
  | NoDup _ ?l => name (`_NoDup` ++ l#n)
  end.
>>
(* Overwrite the definition of rename_hyp using the ::= operator. :*)

<<
Ltac rename_hyp ::= my_rename_hyp.
>> *)

Ltac2 Type rename_directive := [ String(string) | RecRename(int,constr) ].
Ltac2 Type rename_directives := rename_directive list.

Ltac2 Type hypnames := string list.
Ltac2 mutable add_suffix := true.

(* Elements of l are supposed to already start with "_" *)
Ltac2 build_name_gen (sep:string) (suffx:bool) (l:string list) :=
  String.app (String.concat sep l) (if suffx then "_" else "").

Ltac2 build_name l := build_name_gen "_" add_suffix (List.rev l).
Ltac2 build_name_no_suffix l := build_name_gen "_" false (List.rev l).

(* This sets the way numerical constants are displayed, default value
   is set below to numerical_names_nosufx, which will give the same
   name to (O<1)%nat and (O<1)%Z and (O<1)%N, i.e. h_lt_0_1_.

   but you can use this in your development to change it
   h_lt_0n_1n_/h_lt_0z_1z_/h_lt_0N_1N_:
   Ltac numerical_names ::= numerical_names_sufx *)

Ltac2 Type numerical_names_style := bool.
Ltac2 mutable numerical_names := false.

Ltac2 string_of_int (i:int) := Message.to_string (Message.of_int i).

(** Generate fresh name for numerical constants.

   Warning: problem here: hyps names may end with a digit: Coq may
   *replace* the digit in case of name clash. If you are bitten by
   this, you should switch to "Ltac add_suffix ::= constr:(true)." so
   that every hyp name ends with "_", so that coq never mangle with
   the digits *)
Ltac2 num_nosufx (i:int) :=
  msgs ".   num_nosufx";
  printf "<infomsg>.    i = %s</infomsg>" (string_of_int i);
  let res := String.app "_" (string_of_int i) in
  printf "<infomsg>.    res = %s</infomsg>" res;
  msgs ".   num_nosufx: end";
  res.
(* Ltac2 num_sufx (i:int) (sfx:string) := (String.app (string_of_int i) sfx). *)


(* TODO: find a way to make a string from nat, Z and N *)
Ltac2 numerical_names_nosufx (t:constr):string :=
  printf  "<infomsg>...NUM: %t</infomsg>" t;
  if is_closed t then
    match! t with
    | 0%Z => "0"
    | 1%Z => "1"
    | 2%Z => "2"
    | 3%Z => "3"
    | 4%Z => "4"
    | 5%Z => "5"
    | 6%Z => "6"
    | 7%Z => "7"
    | 8%Z => "8"
    | 9%Z => "9"
    | 10%Z => "10"
    | O%nat => "0"
    | 1%nat => "1"
    | 2%nat => "2"
    | 3%nat => "3"
    | 4%nat => "4"
    | 5%nat => "5"
    | 6%nat => "6"
    | 7%nat => "7"
    | 8%nat => "8"
    | 9%nat => "9"
    | 10%nat => "10"
    | O%N => "0"
    | 1%N => "1"
    | 2%N => "2"
    | 3%N => "3"
    | 4%N => "4"
    | 5%N => "5"
    | 6%N => "6"
    | 7%N => "7"
    | 8%N => "8"
    | 9%N => "9"
    | 10%N => "10"
    | _ => backtrack "not recognized as a number "
    end
  else
    backtrack "not a nameable number".

Ltac2 numerical_names_sufx t :=
  match! t with
  | 0%Z => "0z"
  | 1%Z => "1z"
  | 2%Z => "2z"
  | 3%Z => "3z"
  | 4%Z => "4z"
  | 5%Z => "5z"
  | 6%Z => "6z"
  | 7%Z => "7z"
  | 8%Z => "8z"
  | 9%Z => "9z"
  | 10%Z => "10z"
  (* | Z0 => num_sufx 0 *)
  | O%nat => "0n"
  | 1%nat => "1n"
  | 2%nat => "2n"
  | 3%nat => "3n"
  | 4%nat => "4n"
  | 5%nat => "5n"
  | 6%nat => "6n"
  | 7%nat => "7n"
  | 8%nat => "8n"
  | 9%nat => "9n"
  | 10%nat => "10n"
  | O%N => "0N"
  | 1%N => "1N"
  | 2%N => "2N"
  | 3%N => "3N"
  | 4%N => "4N"
  | 5%N => "5N"
  | 6%N => "6N"
  | 7%N => "7N"
  | 8%N => "8N"
  | 9%N => "9N"
  | 10%N => "10N"
  end.

(* Redefine at will *)
Ltac2 add_numerical_names (): constr -> string:=
  if numerical_names then numerical_names_sufx else numerical_names_nosufx.


(** This determines the depth of the recursive analysis of a type to
    compute the corresponding hypothesis name. generally 2 or 3 is
    enough. More gives too log names, less may give identical names
    too often. *)
Ltac2 mutable rename_depth := 3.

(** Default prefix for hypothesis names. *)
Ltac2 default_prefix():string := "h".

(** A few special default chunks, for special cases in the naming heuristic. *)
Ltac2 impl_prefix() := "impl".
Ltac2 forall_prefix() := "all".
Ltac2 exists_prefix() := "ex".


(** This is the customizable naming tactic that the user should
    REDEFINE along his development. See above for an example of such
    redefinition. It should always fail when no name suggestion is
    found, to give a chance to the default naming scheme to apply. *)
Ltac2 mutable rename_hyp (stop:int)  (th:constr): rename_directives := backtrack "rename_hyp".
Ltac2 mutable rename_hyp_default (n:int) (th:constr): rename_directives := backtrack "rename_hyp_default".

(* TODO: find something better to detect implicits!! *)
(* Determines the number of non "head" implicit arguments, i.e. implicit
   arguments that are before any explicit one. This shall be ignored
   when naming an application. This is done in very ugly way. Any
   better solution welcome. *)
Ltac2 count_impl th :=
  (*  match Unsafe.kind th with | App _ args => Array.length args | _ => 0  end. *)
  match Unsafe.kind th with
  | App _ _ => 
      lazy_match! th with
      | (?z _ _ _ _ _ _ _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ _ _ _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ _ _ _ _ _ j k)) in 2
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ _ _ _ _ i j k)) in 3
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ _ _ _ h i j k)) in 4
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ _ _ g h i j k)) in 5
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ _ f g h i j k)) in 6
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ _ e f g h i j k)) in 7
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ _ d e f g h i j k)) in 8
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ _ c d e f g h i j k)) in 9
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z _ b c d e f g h i j k)) in 10
          | _ => let _ := constr:(fun a b c d e f g h i j k => ($z a b c d e f g h i j k , $z a b c d e f g h i j k)) in 11
          end
      | (?z _ _ _ _ _ _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ _ _ _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ _ _ _ _ _ j k)) in 2
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ _ _ _ _ i j k)) in 3
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ _ _ _ h i j k)) in 4
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ _ _ g h i j k)) in 5
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ _ f g h i j k)) in 6
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ _ e f g h i j k)) in 7
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ _ d e f g h i j k)) in 8
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z _ c d e f g h i j k)) in 9
          | _ => let _ := constr:(fun b c d e f g h i j k => ($z b c d e f g h i j k , $z b c d e f g h i j k)) in 10
          end
      | (?z _ _ _ _ _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ _ _ _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ _ _ _ _ _ j k)) in 2
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ _ _ _ _ i j k)) in 3
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ _ _ _ h i j k)) in 4
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ _ _ g h i j k)) in 5
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ _ f g h i j k)) in 6
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ _ e f g h i j k)) in 7
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z _ d e f g h i j k)) in 8
          | _ => let _ := constr:(fun c d e f g h i j k => ($z c d e f g h i j k , $z c d e f g h i j k)) in 9
          end
      | (?z _ _ _ _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ _ _ _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ _ _ _ _ _ j k)) in 2
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ _ _ _ _ i j k)) in 3
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ _ _ _ h i j k)) in 4
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ _ _ g h i j k)) in 5
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ _ f g h i j k)) in 6
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z _ e f g h i j k)) in 7
          | _ => let _ := constr:(fun d e f g h i j k => ($z d e f g h i j k , $z d e f g h i j k)) in 8
          end
      | (?z _ _ _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z _ _ _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z _ _ _ _ _ j k)) in 2
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z _ _ _ _ i j k)) in 3
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z _ _ _ h i j k)) in 4
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z _ _ g h i j k)) in 5
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z _ f g h i j k)) in 6
          | _ => let _ := constr:(fun e f g h i j k => ($z e f g h i j k , $z e f g h i j k)) in 7
          end
      | (?z _ _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun f g h i j k => ($z f g h i j k , $z _ _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun f g h i j k => ($z f g h i j k , $z _ _ _ _ j k)) in 2
          | _ => let _ := constr:(fun f g h i j k => ($z f g h i j k , $z _ _ _ i j k)) in 3
          | _ => let _ := constr:(fun f g h i j k => ($z f g h i j k , $z _ _ h i j k)) in 4
          | _ => let _ := constr:(fun f g h i j k => ($z f g h i j k , $z _ g h i j k)) in 5
          | _ => let _ := constr:(fun f g h i j k => ($z f g h i j k , $z f g h i j k)) in 6
          end
      | (?z _ _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun g h i j k => ($z g h i j k , $z _ _ _ _ k)) in 1
          | _ => let _ := constr:(fun g h i j k => ($z g h i j k , $z _ _ _ j k)) in 2
          | _ => let _ := constr:(fun g h i j k => ($z g h i j k , $z _ _ i j k)) in 3
          | _ => let _ := constr:(fun g h i j k => ($z g h i j k , $z _ h i j k)) in 4
          | _ => let _ := constr:(fun g h i j k => ($z g h i j k , $z g h i j k)) in 5
          end
      | (?z _ _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun h i j k => ($z h i j k , $z _ _ _ k)) in 1
          | _ => let _ := constr:(fun h i j k => ($z h i j k , $z _ _ j k)) in 2
          | _ => let _ := constr:(fun h i j k => ($z h i j k , $z _ i j k)) in 3
          | _ => let _ := constr:(fun h i j k => ($z h i j k , $z h i j k)) in 4
          end
      | (?z _ _ _) =>
          match! th with
          | _ => let _ := constr:(fun a b c => ($z a b c, $z _ _ c)) in 1
          | _ => let _ := constr:(fun a b c => ($z a b c, $z _ b c)) in 2
          | _ => let _ := constr:(fun a b c => ($z a b c, $z a b c)) in 3
          end
      | (?z _ _) =>
          match! th with
          | _ => let _ := constr:(fun a b => ($z a b, $z _ b)) in 1
          | _ => let _ := constr:(fun a b => ($z a b, $z a b)) in 2
          end
      | (?z _) =>
          match! th with
          | _ => let _ := constr:(fun b => ($z b, $z _)) in 0
          | _ => let _ := constr:(fun b => ($z b, $z b)) in 1
          end
      end
  | _ => 0
  end.



Ltac2 percent():char := (Char.of_int 37).
Ltac2 arobase():char := (Char.of_int 64).
Ltac2 space():char := (Char.of_int 32).
Ltac2 parg():char := (Char.of_int 40).
Ltac2 pard():char := (Char.of_int 41).

(* Ltac2 Eval (Char.to_int (String.get ")" 0)). *)

Ltac2 set_forbidden_chars (): char list := [space();pard();parg()].
Ltac2 set_removable_chars (): char list := [percent();arobase()].
Ltac2 set_suspect_chars (): char list := List.append (set_forbidden_chars()) (set_removable_chars()).
Ltac2 set_forbidden_charints (): int list := List.map Char.to_int (set_forbidden_chars()).
Ltac2 set_removable_charints (): int list := List.map Char.to_int (set_removable_chars()).
Ltac2 set_suspect_charints (): int list := List.map Char.to_int (set_suspect_chars()).

Ltac2 string_forall (p:char -> bool) (s:string) : bool :=
  let rec check i :=
    if Int.ge i (String.length s) then true
    else if p (String.get s i) then check (Int.add 1 i) else false
    in
  check 0.

Ltac2 string_count_if (p:char -> bool) (s:string) : int :=
  let lgth := String.length s in
  let rec count acc i :=
    if Int.ge i lgth then acc
    else if p (String.get s i) then count (Int.add 1 acc) (Int.add 1 i)
         else  count acc (Int.add 1 i)
  in
  count 0 0.

Ltac2 string_remove (p:char -> bool) (s:string) : string :=
  let lgth := String.length s in  
  let nbgood := string_count_if (fun c => Bool.neg (p c)) s in
  let res := String.make nbgood (arobase()) in
  let rec fill k i: unit :=
    if Int.ge i lgth then ()
    else
      let c := String.get s i in
      if p c then fill k (Int.add 1 i)
      else (String.set res k c; fill  (Int.add 1 k)  (Int.add 1 i)) in
  fill 0 0;
  res.

Ltac2 forbidden_charint (c:char):bool := (List.mem Int.equal (Char.to_int c) (set_forbidden_charints())).
Ltac2 removeable_charint (c:char):bool := (List.mem Int.equal (Char.to_int c) (set_removable_charints())).
Ltac2 suspect_charint (c:char):bool := (List.mem Int.equal (Char.to_int c) (set_suspect_charints())).
  
Ltac2 Eval (string_remove (fun c => (Char.equal c (arobase()))) "az@er% % @o").
Ltac2 Eval (string_remove forbidden_charint "az@er% % @o").
Ltac2 Eval (string_remove suspect_charint "az@er% % @o").




(* Ltac2 print_id (t:constr) : string option := *)
(*   let (idopt,_) := Fresh.next (Fresh.Free.empty) t in *)
(*   Some (Ident.to_string idopt). *)

(** Build a chunk from a simple term: either a number or a freshable
   term. *)
Ltac2 box_name t : string :=
  let s:string := Message.to_string (fprintf "%t" t) in
  let s := if Char.equal (String.get s 0) (arobase())
          then String.sub s 1 (Int.sub (String.length s) 1)
          else  s in
  match Ident.of_string s with
  | Some _ => s
  | None =>
      match Unsafe.kind t with 
      | Unsafe.Constant cstt _ =>
          let id:ident := List.last (Env.path (Std.ConstRef cstt)) in
          Ident.to_string id
      | Unsafe.Var id => Ident.to_string id
      | Unsafe.Ind _ _ =>
          printf "<infomsg>IND: %t</infomsg>" t;
          let s:string := Message.to_string (fprintf "%t" t) in
          let s := if Char.equal (String.get s 0) (arobase())
                   then String.sub s 1 (Int.sub (String.length s) 1)
                   else  s in
          s
      | _ =>
          if is_closed t then
            printf "<infomsg>.    BEFORE NUM %t</infomsg>" t;
            let s := add_numerical_names () t in
            printf "<infomsg>.    AFTER NUM %t -> %s</infomsg>" t s;
            s
          else backtrack "cannot be a number"
      end
  end.

(* Ltac2 id_of_constr (t:constr) : string option := *)
(*   let s:string := Message.to_string (fprintf "%t" t) in *)
(*   if string_forall (fun c => Bool.neg (forbidden_charint c)) s *)
(*   then  *)
(*     let s := string_remove removeable_charint s in *)
(*     if string_forall (fun c => Bool.neg (Char.equal (space()) c)) s then Some s else None *)
(*     else None. *)


Local Ltac2 is_dep_prod (t:constr): bool :=
  match kind t with
  | Prod _ subt => Bool.neg (is_closed subt)
  | _ => false
  end.



Ltac2 is_hyp (id:ident) :=
  let hyps := Control.hyps () in
  List.exist (fun (x,_,_) => Ident.equal id x) hyps.

(** Default naming of an application: we name the function if possible
   or fail, then we name all parameters that can be named either
   recursively or simply. Parameters at positions below nonimpl are
   considered implicit and not considered. *)
Ltac2 rec rename_app (nonimpl:int) (stop:int) (acc:string list ref) th: unit :=
  Control.plus (fun () => let s := box_name th in
                          Ref.set acc (s:: Ref.get acc))
    (fun _ =>
       match Unsafe.kind th with
       | App f args =>
           (* control_try? *)
           (let fun_name:string := box_name f in
            Ref.set acc (fun_name:: Ref.get acc));
           let newstop:int := Int.sub stop 1 in
           let nonimplicitsargs := Array.sub args (Int.sub (Array.length args) nonimpl) nonimpl in
           Array.iter (fun arg => (fallback_rename_hyp newstop acc arg)) nonimplicitsargs
       | _ => control_try (fun() => Ref.set acc (box_name th :: Ref.get acc))
       end)
    
    (** ** Calls the (user-defined) rename_hyp + and fallbacks to some default
        namings if needed. [h] is the hypothesis (ident) to rename, [th] is its
        type. *)
with rename_hyp_chained_quantifs stop (acc:string list ref) (th:constr) : unit :=
    let newstop := Int.sub stop 1 in
    match Unsafe.kind th with
    | Prod bnd subth =>
        if is_dep_prod th
        then
          let nme:ident := Option.get(Binder.name bnd) in
          let typ := Binder.type bnd in
          (* If there is already a hyp named nme, we rename it so that the
             'in_context nme ...' below does not fail. We could rename the
             other way around but we prefer keeping the name found in the
             binder. *)
          (if is_hyp nme then Std.rename [(nme , Fresh.in_goal nme)] else ()) ;
          (* Ref.set acc (Ident.to_string nme :: Ref.get acc); *)
          let tac_under_binder :=
              fun () =>
                let nme_c:constr := Unsafe.make (Var(nme)) in
                let subth' := Constr.Unsafe.substnl [nme_c] 0 subth in
                rename_hyp_chained_quantifs stop acc subth' in
           (in_context nme typ tac_under_binder);
           ()
        else
          rename_hyp_chained_quantifs stop acc subth
    | _ => fallback_rename_hyp stop acc th
    end

with fallback_rename_hyp_quantif stop (acc:string list ref) (th:constr) : unit :=
    let newstop := Int.sub stop 1 in
    match Unsafe.kind th with
    | Prod bnd subth =>
        if is_dep_prod th
        then
          let nme:ident := Option.get(Binder.name bnd) in
          let typ := Binder.type bnd in
          (* If there is already a hyp named nme, we rename it so that the
             'in_context nme ...' below does not fail. We could rename the
             other way around but we prefer keeping the name found in the
             binder. *)
          (if is_hyp nme then Std.rename [(nme , Fresh.in_goal nme)] else ()) ;
          Ref.set acc ((*Ident.to_string nme ::*) forall_prefix() :: Ref.get acc);
         let tac_under_binder :=
              fun () =>
                let nme_c:constr := Unsafe.make (Var(nme)) in
                let subth' := Constr.Unsafe.substnl [nme_c] 0 subth in
                rename_hyp_chained_quantifs newstop acc subth' in
           (in_context nme typ tac_under_binder);
           ()

        else
          (Ref.set acc (impl_prefix() :: Ref.get acc);
           rename_hyp_chained_quantifs newstop acc subth)
    | App f args =>
        match Unsafe.kind f, Unsafe.kind constr:(@Init.Logic.ex) with
        | Ind ind _, Ind ind' _ =>
            if Ind.equal ind ind'
            then (
                msgs "EXXXX";
                Ref.set acc ((*Ident.to_string a ::*) exists_prefix() :: Ref.get acc);
                  match Unsafe.kind (Array.get args 1) with
                  | Lambda bnd subth => rename_hyp_chained_quantifs newstop acc subth
                  | _ => backtrack "not exist"
                  end)
            else backtrack "not exist"
        | _ => backtrack "not exist"
        end
    | _ => backtrack "no quantif"
    end


with fallback_rename_hyp_specials stop (acc:string list ref) th :unit :=
    let newstop := Int.sub stop 1 in
    Control.plus 
       (* First see if user has something that applies *)
       (fun() => let dirs := rename_hyp newstop th in
                 interp_directives acc (List.rev dirs) )
       (* if it fails try default specials *)
       (fun _ => let dirs := rename_hyp_default newstop th in
                 interp_directives acc (List.rev dirs))

with fallback_rename_hyp stop (acc:string list ref) th:unit :=
          if Int.le stop 0 then ()
          else
            Control.plus (fun () => fallback_rename_hyp_specials stop acc th)
              (fun _ => match! th with
                        | forall _, _ => fallback_rename_hyp_quantif stop acc th
                        | exists _, _ => fallback_rename_hyp_quantif stop acc th
                        | _ => let numnonimpl := count_impl th in
                               let _ := rename_app numnonimpl stop acc th in
                               ()
                        end)

with interp_directives acc ld:unit :=
  List.fold_right (fun d _ => interp_directive acc d) ld ()

with interp_directive acc d :=
  match d with
  | String s => Ref.set acc (s :: (Ref.get acc))
  | RecRename n t => fallback_rename_hyp n acc t
  end.

Ltac2 rename_acc n th :=
  let acc := Ref.ref [] in
  (* Here we intentionally create a separate goal to discard all side
  effect (renames) ont he current goal. The constr actually returned by in_context does not matter. *)
  let _ := in_context (Option.get (Ident.of_string "DUMMY_SUBGOAL")) constr:(Prop) (fun () => fallback_rename_hyp n acc th) in
  Ref.get acc.

Ltac2 fallback_rename_hyp_name th: ident :=
  let depth := rename_depth in
  msgs "ICI 1";
  let l := rename_acc depth th in
  msgs "ICI10";
  match l with
    [] => backtrack "No name built"
  | _ => (printf   "<infomsg>FINAL acc = %a</infomsg>" (pr_list pr_string) l;
         let nme := String.app "h_" (build_name l) in
         let id := Option.get (Ident.of_string nme) in
         Fresh.in_goal id)
  end.

Ltac2 rename_hyp_with_name h th := fail.

(* Tactic renaming hypothesis H. Ignore Type-sorted hyps, fails if no
renaming can be computed. Example of failing type: H:((fun x => True) true). *)
Ltac2 autorename_strict (h:ident) :=
  let th := Constr.type (Control.hyp h) in
  let tth := Constr.type th in
  printf "<infomsg>th = %t</infomsg>" tth ;
  match! tth with
    (* | _ => *)
    (*   let l := rename_hyp_with_name $h th in *)
    (*   let dummy_name := fresh "dummy" in *)
    (*   rename $h into dummy_name; (* frees current name of H, in case of idempotency *) *)
    (*   let newname := build_name_no_suffix l in *)
    (*   rename dummy_name into newname *)
  | Prop =>
      let dummy_name := Fresh.in_goal (Option.get (Ident.of_string "dummy")) in
      Std.rename [(h , dummy_name)]; (* frees current name of H, in case of idempotency *)
      let newname := fallback_rename_hyp_name th in
      Std.rename [(dummy_name,newname)]
  | Prop =>
      let msg := fprintf "no renaming pattern for %I : %t" h th in
      backtrack (Message.to_string msg)
  (* | _ => () (* not in Prop or "no renaming pattern for " $h *) *)
  end.

(* Tactic renaming hypothesis H. *)

Ltac2 ltac2_autorename (h:ident) :=
  control_try (fun () => autorename_strict h).

Ltac2 ltac1_autorename (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  ltac2_autorename h.


Tactic Notation "autorename" hyp(h) :=
  let tac := ltac2:(h |- ltac1_autorename h) in
  tac h.

Ltac2 decr (n:int):int :=
  if Int.equal n 0 then 0 else Int.sub n 1.

Ltac2 rename_list l acc s :=
  List.iter (fun (n,t) => fallback_rename_hyp n acc t) l;
  Ref.set acc (s :: (Ref.get acc)).



(* Ltac2 Notation x(constr) "#" y(tactic(1)) := (RecRename x y). *)


Ltac2 Set rename_hyp_default :=
  fun n th: rename_directives =>
    if Int.lt n 0 then []
    else
      match! th with
      | ?x <> ?y => [String "neq"; RecRename (decr n) x; RecRename (decr n) y] 
      | @cons _ ?x (cons ?y ?l) => [String "cons"; RecRename n x; RecRename n y; RecRename (decr (decr n)) l]
      | @cons _ ?x ?l => if Int.ge n 1 then [String "cons"; RecRename n x; RecRename (decr n) l] else [String "cons"]
      | (@Some _ ?x) =>  [RecRename (Int.add 1 n) x]
      | (@None _) => [String "None"]
      end.

Definition DUMMY: Prop -> Prop.
  exact (fun x:Prop => x).
Qed.

Ltac2 recRename n x :=
  RecRename (Option.get (Ltac1.to_int n)) (Option.get (Ltac1.to_constr x)).


(* ********** CUSTOMIZATION ********** *)

(** If this is true, then all hyps names will have a trailing "_". In
    case of names ending with a digit (like in "le_1_2" or "le_x1_x2")
    this additional suffix avoids Coq's fresh name generation to
    *replace* the digit. Although this is esthetically bad, it makes
    things more predictable. You may set this to true for backward
    compatility. *)



(* TESTS *)

(* This settings should reproduce the naming scheme of libhypps-1.0.0
   and libhypps-1.0.1. *)
Ltac2 Set add_suffix := false.
Ltac2 Set numerical_names := true.

(* From there this is LibHypTest from 1f7a1ed2289e439c291fcbd06c51705547feef1e *)
Ltac2 rename_hyp_2 n th :=
  match! th with
  | true <> false => [String "tNEQf"]
  | true = false => [String "tEQf"]
  end.

Ltac2 Set rename_hyp := rename_hyp_2.

(* Suppose I want to add later another naming rule: *)
Ltac2 rename_hyp_3 n th :=
  match! th with
  | Nat.eqb ?x ?y = true => [String "Neqb" ; RecRename n x ; RecRename n y]
  | true = Nat.eqb ?x ?y => [String "Neqb" ; RecRename n x ; RecRename n y]
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_3.

Ltac2 Set rename_depth := 3.

Close Scope Z_scope.
Open Scope nat_scope.
Lemma dummy: forall x y,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
    Some x = Some y ->
    0 = 1 ->
    (0 = 1)%Z ->
    ~x = y ->
    true = Nat.eqb 3 4  ->
    Nat.eqb 3 4 = true  ->
    true = Nat.leb 3 4  ->
    1 = 0 ->
    ~x = y ->
    ~1 < 0 ->
     (forall w w':nat , w = w' -> ~true=false) ->
     (forall w w':nat , w = w' -> true=false /\ True) ->
     (forall w w':nat , w = w' -> False /\ True) ->
     (exists w:nat , w = w -> ~(true=(andb false true)) /\ False) ->
     (exists w:nat , w = w -> True /\ False) ->
     (forall w w':nat , w = w' -> true=false) ->
     (forall w w':nat , w = w' -> Nat.eqb 3 4=Nat.eqb 4 3) ->
    List.length (cons 3 nil) = (fun x => 0)1 ->
    List.length (cons 3 nil) = 0 ->
    plus 0 y = y ->
    (true=false) ->
    (False -> (true=false)) ->
    forall (x : nat) (env : list nat),
      ~ List.In x nil ->
      cons x (cons 3 env) = cons 2 env ->
    forall z t:nat, IDProp ->
      (0 < 1 -> 0 < 0 -> true = false -> ~(true=false)) ->
      (~(true=false)) ->
      (forall w w',w < w' -> ~(true=false)) ->
      (0 < 1 -> ~(1<0)) ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
  intros;{(fun h => autorename h)}.

  match type of x with nat => idtac | _ => fail "test failed!" end.
  match type of y with nat => idtac | _ => fail "test failed!" end.
  match type of h_le_0n_1n with 0 <= 1 => idtac | _ => fail "test failed!" end.
  match type of h_le_0z_1z with (0 <= 1)%Z => idtac | _ => fail "test failed!" end.
  match type of h_le_x_y with x <= y => idtac | _ => fail "test failed!" end.
  match type of h_eq_x_y with x = y => idtac | _ => fail "test failed!" end.
  match type of h_eq_0n_1n with 0 = 1 => idtac | _ => fail "test failed!" end.
  match type of h_eq_0z_1z with 0%Z = 1%Z => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_3n_4n with true = (3 =? 4) => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_3n_4n0 with (3 =? 4) = true => idtac | _ => fail "test failed!" end.
  match type of h_eq_true_leb_3n_4n with true = (3 <=? 4) => idtac | _ => fail "test failed!" end.
  match type of h_eq_1n_0n with 1 = 0 => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y0 with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_not_lt_1n_0n with ~ 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_all_tNEQf with forall w w' : nat, w = w' -> true <> false => idtac | _ => fail "test failed!" end. 
  match type of h_all_and_tEQf_True with forall w w' : nat, w = w' -> true = false /\ True => idtac | _ => fail "test failed!" end.
  match type of h_eq_cons_x0_3n_cons_2n with x0 :: 3 :: env = 2 :: env => idtac | _ => fail "test failed!" end.

  match type of h_all_and_False_True with forall w w' : nat, w = w' -> False /\ True => idtac | _ => fail "test failed!" end.
  match type of h_ex_and_neq_False with exists w : nat, w = w -> true <> (false && true)%bool /\ False => idtac | _ => fail "test failed!" end.
  match type of h_ex_and_True_False with exists w : nat, w = w -> True /\ False => idtac | _ => fail "test failed!" end.
  match type of h_all_tEQf with forall w w' : nat, w = w' -> true = false => idtac | _ => fail "test failed!" end.
  match type of h_all_eq_eqb_eqb with forall w w' : nat, w = w' -> (3 =? 4) = (4 =? 3) => idtac | _ => fail "test failed!" end.
  (* match type of h_eq_length_cons_1n with length (3::nil) = (fun _ : nat => 0) 1 => idtac | _ => fail "test failed!" end. *)
  match type of h_eq_length_cons_0n with length (3::nil) = 0 => idtac | _ => fail "test failed!" end.
  match type of h_eq_add_0n_y_y with 0 + y = y => idtac | _ => fail "test failed!" end.
  match type of h_tEQf with true = false => idtac | _ => fail "test failed!" end.
  match type of h_impl_tEQf with False -> true = false => idtac | _ => fail "test failed!" end.
  match type of x0 with nat => idtac | _ => fail "test failed!" end.
  match type of env with list nat => idtac | _ => fail "test failed!" end.
  match type of h_not_In_x0_nil with ~ In x0 nil => idtac | _ => fail "test failed!" end.
  match type of h_eq_cons_x0_3n_cons_2n with x0 :: 3 :: env = 2 :: env => idtac | _ => fail "test failed!" end.
  match type of h_IDProp with IDProp => idtac | _ => fail "test failed!" end.
  match type of h_impl_tNEQf with 0 < 1 -> 0 < 0 -> true = false -> true <> false => idtac | _ => fail "test failed!" end.
  match type of h_tNEQf with true <> false => idtac | _ => fail "test failed!" end.
  match type of h_all_tNEQf0 with forall w w' : nat, w < w' -> true <> false => idtac | _ => fail "test failed!" end.
  match type of h_impl_not_lt with 0 < 1 -> ~ 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_impl_lt_1n_0n with 0 < 1 -> 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_lt_0n_z with 0 < z => idtac | _ => fail "test failed!" end.
  exact I.
Qed. 


(*
(* Ltac autorename h := *)
  (* let tac := ltac2:(h |- ltac2_autorename h) in *)
  (* tac h. *)

  (* Unset Printing Notations. *)

(* Ltac2 Eval (count_impl constr:(3 + 4)). *)

Parameters X Y: nat -> Prop.
Parameters PX: X 3.
Parameters PY: Y 3.


Goal forall [A : Type] (P Q : A -> Prop) (x : A), P x -> Q x -> (exists2 x : A, P x & Q x) -> ex2 P Q -> False.

  intros A P Q x H H0 H1 H2.

  autorename H1.
  autorename H2.
  autorename H.
  autorename H0.
  assert (HH: (fun x => x = x) 1).
  2:{ autorename HH.
  

  ltac2:(let l := rename_acc 3 constr:(exists2 x0 : A, P x0 & Q x0) in
         printf "<infomsg>BEFORE BUILDNAME %a </infomsg>" (pr_list pr_string) l;
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 9 constr:(ex2 P Q) in
         printf "<infomsg>BEFORE BUILDNAME %a </infomsg>" (pr_list pr_string) l;
         let nme := build_name l in
         printf "%s" nme).
Abort.

Definition foo := (fun a b:bool => a = b).

Goal forall n m p : nat, forall b:bool, n<m -> m<= p -> True .
Proof.
  intros n m p b H H0.

  assert (forall z, foo b z).
  2:{ 

  ltac2:(let l := rename_acc 4 constr:(forall b:nat, Nat.clearbit b 4%nat = 0) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).

  Unset Printing Notations.




  ltac2:(let l := rename_acc 9 constr:(Nat.clearbit n m = p) in
         printf "<infomsg>BEFORE BUILDNAME %a </infomsg>" (pr_list pr_string) l;
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 3 constr:(Nat.clearbit 3 4%nat = 0) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 4 constr:(Nat.clearbit 3 4%nat = 0 -> Nat.clearbit 3 4%nat = 7) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 3 constr:(forall x:nat, Nat.clearbit x 4%nat = 0) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 3 constr:(forall b:nat, Nat.clearbit b 4%nat = 0) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).


  ltac2:(let l := rename_acc 4 constr:(forall b:nat, Nat.clearbit b 4%nat = 0) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 4 constr:(forall x:nat, Nat.clearbit x 4%nat = 0) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).

  ltac2:(let l := rename_acc 4 constr:(forall x:Z, BinIntDef.Z.quot x x = 1%Z) in
         printf "BEFORE BUILDNAME";
         let nme := build_name l in
         printf "%s" nme).


  ltac2:(let l := rename_acc 4 constr:(Nat.clearbit 3%nat 4%nat) in
         let nme := build_name l in
         printf "%s" nme).
Abort.


*)



(** This is the customizable naming tactic that the user should
    REDEFINE along his development. See above for an example of such
    redefinition. It should always fail when no name suggestion is
    found, to give a chance to the default naming scheme to apply. *)
Ltac rename_hyp stop th := fail.
(** This will later contain a few default fallback naming strategy. *)
Ltac rename_hyp_default stop th :=
  fail.

(** Builds an id from a sequence of chunks. fresh is not supposed to
    add suffixes anywhere because all the ids we use start with "_".
    As long as no constant or hyp name start with "_" it is ok. *)
Ltac build_name_gen suffx l :=
  let l := eval lazy beta delta [List.app] iota in l in
  match l with
  | nil => fail
  | (forall id1:Prop, DUMMY id1)::nil =>
    match suffx with
    | true => fresh id1 "_"
    | false => fresh id1
    end
  | (forall id1:Prop, DUMMY id1)::?l' =>
    let recres := build_name_gen suffx l' in
    (* id1 starts with "_", so fresh do not add any suffix *)
    let res := fresh id1 recres in
    res
  end.


Ltac build_name l := build_name_gen add_suffix l.
Ltac build_name_no_suffix l := build_name_gen constr:(false) l.



(** * Implementation principle:

   The name of the hypothesis will be a sequence of chunks. A chunk is
   a word generally starting with "_".

   Internally (not seen by the user) this sequence is represented by a
   list of small terms. One term of the form (∀ <chunk>:Prop, DUMMY
   <chunk>) per chunk. For instance the sequence "h_eq_foo" is
   represented by the following coq term:

   [(∀ h,DUMMY h) ; (∀ _eq,DUMMY _eq) ; (∀ _foo, DUMMY _foo)]

   where DUMMY is an opaque (identity) function but we don't care. *)


(** We define DUMMY as an opaque symbol. *)
Definition DUMMY: Prop -> Prop.
  exact (fun x:Prop => x).
Qed.

(* ********** CUSTOMIZATION ********** *)

(** If this is true, then all hyps names will have a trailing "_". In
    case of names ending with a digit (like in "le_1_2" or "le_x1_x2")
    this additional suffix avoids Coq's fresh name generation to
    *replace* the digit. Although this is esthetically bad, it makes
    things more predictable. You may set this to true for backward
    compatility. *)
Ltac add_suffix := constr:(true).

(* This sets the way numerical constants are displayed, default value
   is set below to numerical_names_nosufx, which will give the same
   name to (O<1)%nat and (O<1)%Z and (O<1)%N, i.e. h_lt_0_1_.

   but you can use this in your development to change it
   h_lt_0n_1n_/h_lt_0z_1z_/h_lt_0N_1N_:
   Ltac numerical_names ::= numerical_names_sufx *)
Ltac numerical_names := fail.

(** This determines the depth of the recursive analysis of a type to
    compute the corresponding hypothesis name. generally 2 or 3 is
    enough. More gives too log names, less may give identical names
    too often. *)
Ltac rename_depth := constr:(3).

(** Default prefix for hypothesis names. *)
Ltac default_prefix :=constr:(forall h, DUMMY h).

(** A few special default chunks, for special cases in the naming heuristic. *)
Ltac impl_prefix := constr:(forall _impl, DUMMY _impl).
Ltac forall_prefix := constr:(forall _all, DUMMY _all).
Ltac exists_prefix := constr:(forall _ex, DUMMY _ex).

(** This is the customizable naming tactic that the user should
    REDEFINE along his development. See above for an example of such
    redefinition. It should always fail when no name suggestion is
    found, to give a chance to the default naming scheme to apply. *)

 Ltac rename_hyp stop th := fail.

(* ************************************** *)


(** Builds an id from a sequence of chunks. fresh is not supposed to
    add suffixes anywhere because all the ids we use start with "_".
    As long as no constant or hyp name start with "_" it is ok. *)
Ltac build_name_gen suffx l :=
  let l := eval lazy beta delta [List.app] iota in l in
  match l with
  | nil => fail
  | (forall id1:Prop, DUMMY id1)::nil =>
    match suffx with
    | true => fresh id1 "_"
    | false => fresh id1
    end
  | (forall id1:Prop, DUMMY id1)::?l' =>
    let recres := build_name_gen suffx l' in
    (* id1 starts with "_", so fresh do not add any suffix *)
    let res := fresh id1 recres in
    res
  end.

Ltac build_name l := build_name_gen add_suffix l.
Ltac build_name_no_suffix l := build_name_gen constr:(false) l.


(** Check if t is an eligible argument for fresh function. For instance
   if t is (forall foo, ...), it is not eligible. *)
Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

(** Generate fresh name for numerical constants.

   Warning: problem here: hyps names may end with a digit: Coq may
   *replace* the digit in case of name clash. If you are bitten by
   this, you should switch to "Ltac add_suffix ::= constr:(true)." so
   that every hyp name ends with "_", so that coq never mangle with
   the digits *)
Ltac numerical_names_nosufx t :=
  match t with
  | 0%Z => fresh "_0"
  | 1%Z => fresh "_1"
  | 2%Z => fresh "_2"
  | 3%Z => fresh "_3"
  | 4%Z => fresh "_4"
  | 5%Z => fresh "_5"
  | 6%Z => fresh "_6"
  | 7%Z => fresh "_7"
  | 8%Z => fresh "_8"
  | 9%Z => fresh "_9"
  | 10%Z => fresh "_10"
  (* | Z0 => fresh "_0" *)
  | O%nat => fresh "_0"
  | 1%nat => fresh "_1"
  | 2%nat => fresh "_2"
  | 3%nat => fresh "_3"
  | 4%nat => fresh "_4"
  | 5%nat => fresh "_5"
  | 6%nat => fresh "_6"
  | 7%nat => fresh "_7"
  | 8%nat => fresh "_8"
  | 9%nat => fresh "_9"
  | 10%nat => fresh "_10"
  | O%N => fresh "_0"
  | 1%N => fresh "_1"
  | 2%N => fresh "_2"
  | 3%N => fresh "_3"
  | 4%N => fresh "_4"
  | 5%N => fresh "_5"
  | 6%N => fresh "_6"
  | 7%N => fresh "_7"
  | 8%N => fresh "_8"
  | 9%N => fresh "_9"
  | 10%N => fresh "_10"
  end.

Ltac numerical_names_sufx t :=
  match t with
  | 0%Z => fresh "_0z"
  | 1%Z => fresh "_1z"
  | 2%Z => fresh "_2z"
  | 3%Z => fresh "_3z"
  | 4%Z => fresh "_4z"
  | 5%Z => fresh "_5z"
  | 6%Z => fresh "_6z"
  | 7%Z => fresh "_7z"
  | 8%Z => fresh "_8z"
  | 9%Z => fresh "_9z"
  | 10%Z => fresh "_10z"
  (* | Z0 => fresh "_0" *)
  | O%nat => fresh "_0n"
  | 1%nat => fresh "_1n"
  | 2%nat => fresh "_2n"
  | 3%nat => fresh "_3n"
  | 4%nat => fresh "_4n"
  | 5%nat => fresh "_5n"
  | 6%nat => fresh "_6n"
  | 7%nat => fresh "_7n"
  | 8%nat => fresh "_8n"
  | 9%nat => fresh "_9n"
  | 10%nat => fresh "_10n"
  | O%N => fresh "_0N"
  | 1%N => fresh "_1N"
  | 2%N => fresh "_2N"
  | 3%N => fresh "_3N"
  | 4%N => fresh "_4N"
  | 5%N => fresh "_5N"
  | 6%N => fresh "_6N"
  | 7%N => fresh "_7N"
  | 8%N => fresh "_8N"
  | 9%N => fresh "_9N"
  | 10%N => fresh "_10N"
  end.

(* Default value, see above for another possible one.
Ltac numerical_names ::= numerical_names_sufx *)
Ltac numerical_names ::= numerical_names_nosufx.
  

Ltac raw_name X := (constr:((forall X, DUMMY X) :: [])).

(** Build a chunk from a simple term: either a number or a freshable
   term. *)
Ltac box_name t :=
  let id_ :=
      match t with
      | _ => numerical_names t
      | _ =>
        let _ := freshable t in
        fresh "_" t
      end
  in constr:(forall id_:Prop, DUMMY id_).


(** This will later contain a few default fallback naming strategy. *)
Ltac rename_hyp_default stop th :=
  fail.

Ltac decr n :=
  match n with
  | S ?n' => n'
  | 0 => 0
  end.

(* This computes the way we decrement our depth counter when we go
   inside of t. For now we forget the idea of traversing Prop sorted
   terms indefinitely. It gives too long names. *)
Ltac nextlevel n t :=
  let tt := type of t in
  match tt with
 (* | Prop => n *)
  | _ => decr n
  end.


(* Determines the number of "head" implicit arguments, i.e. implicit
   arguments that are before any explicit one. This shall be ignored
   when naming an application. This is done in very ugly way. Any
   better solution welcome. *)
Ltac count_impl th :=
  lazymatch th with
  | (?z ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ _ _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ _ _ _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z _ _ _ d e f g h i j k) in constr:(8%nat)
    | _ => let foo := constr:(z _ _ c d e f g h i j k) in constr:(9%nat)
    | _ => let foo := constr:(z _ b c d e f g h i j k) in constr:(10%nat)
    | _ => let foo := constr:(z a b c d e f g h i j k) in constr:(10%nat)
    end
  | (?z ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ _ _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z _ _ d e f g h i j k) in constr:(8%nat)
    | _ => let foo := constr:(z _ c d e f g h i j k) in constr:(9%nat)
    | _ => let foo := constr:(z b c d e f g h i j k) in constr:(10%nat)
    end
  | (?z ?c ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z _ d e f g h i j k) in constr:(8%nat)
    | _ => let foo := constr:(z c d e f g h i j k) in constr:(9%nat)
    end
  | (?z ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z d e f g h i j k) in constr:(8%nat)
    end
  | (?z ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z e f g h i j k) in constr:(7%nat)
    end
  | (?z ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z f g h i j k) in constr:(6%nat)
    end
  | (?z ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z g h i j k) in constr:(5%nat)
    end
  | (?z ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z h i j k) in constr:(4%nat)
    end
  | (?z ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z i j k) in constr:(3%nat)
    end
  | (?z ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ k) in constr:(1%nat)
    | _ => let foo := constr:(z j k) in constr:(2%nat)
    end
  | (?z ?j) => constr:(1%nat)
  | _ => constr:(0%nat)
  end.


(** Default naming of an application: we name the function if possible
   or fail, then we name all parameters that can be named either
   recursively or simply. Parameters at positions below nonimpl are
   considered implicit and not considered. *)
Ltac rename_app nonimpl stop acc th :=
  match th with
  | ?f => let f'' := box_name f in
          constr:(f''::acc)
  | (?f ?x) =>
    match nonimpl with
    | (S ?nonimpl') =>
      let newstop := nextlevel stop x in
      let namex := match true with
                   | _ => fallback_rename_hyp newstop x
                   | _ => constr:(@nil Prop)
                   end in
      let newacc := constr:(namex ++ acc) in
      rename_app nonimpl' stop newacc f
    | 0%nat => (* don't consider this (implicit) argument *)
      rename_app nonimpl stop acc f
    end
  | _ => constr:(@nil Prop)
  end

(* Go under binder and rebuild a term with a good name inside,
   catchable by a match context. *)
with build_dummy_quantified stop th :=
      lazymatch th with
      | forall __z:?A , ?B =>
        constr:(
          fun __z:A =>
            ltac:(
              let th' := constr:((fun __z => B) __z) in
              let th' := eval lazy beta in th' in
                  let res := build_dummy_quantified stop th' in
                  exact res))
      | ex ?f =>
        match f with
        | (fun __z:?A => ?B) =>
          constr:(
            fun __z:A =>
              ltac:(
                let th' := constr:((fun __z => B) __z) in
                let th' := eval lazy beta in th' in
                    let res := build_dummy_quantified stop th' in
                    exact res))
        end
      | _ => fallback_rename_hyp stop th
      end

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some
    default namings if needed. [h] is the hypothesis (ident) to
    rename, [th] is its type. *)

with fallback_rename_hyp_quantif stop th :=
   let prefx :=
       match th with
       | ?A -> ?B => impl_prefix
       | forall _ , _ => forall_prefix
       | ex (fun _ => _) => exists_prefix
       | _ => fail
       end in
   let newstop := decr stop in
   (* sufx_buried contains a list of dummies *)
   let sufx_buried := build_dummy_quantified newstop th in
   (* FIXME: a bit fragile *)
   let sufx_buried' := eval lazy beta delta [List.app] iota in sufx_buried in
       let sufx :=
           match sufx_buried' with
           | context [ (@cons Prop ?x ?y)] => constr:(x::y)
           end
       in
       constr:(prefx::sufx)

with fallback_rename_hyp_specials stop th :=
     let newstop := decr stop in
     match th with
     (* First see if user has something that applies *)
     | _ => rename_hyp newstop th
     (* if it fails try default specials *)
     | _ => rename_hyp_default newstop th
     end

with fallback_rename_hyp stop th :=
     match stop with
     (*| 0 => constr:(cons ltac:(box_name th) nil)*)
     | 0 => constr:(@nil Prop)
     | S ?n =>
       match th with
       | _ => fallback_rename_hyp_specials stop th
       | _ => fallback_rename_hyp_quantif stop th
       | _ =>
         (*let newstop := nextlevel stop th in*)
         let numnonimpl := count_impl th in
         rename_app numnonimpl stop (@nil Prop) th
       end
     end.

(** * Notation to define specific naming strategy *)
Declare Scope autonaming_scope.
(** Notation to build a singleton chunk list *)

(* from coq-8.13 we should use name instead of ident. But let us wait
   a few versions before this change. *)
Notation "'`' idx '`'" := (@cons Prop (forall idx:Prop, DUMMY idx) (@nil Prop))
                           (at level 1,idx name,only parsing): autonaming_scope.


(** Notation to call naming on a term X, with a given depth n. *)
Notation " X '#' n " := ltac:(
                          let c := fallback_rename_hyp n X in exact c)
                            (at level 1,X constr, only parsing): autonaming_scope.

Notation " X '##' " := 
   ltac:(let c := raw_name X in exact c)
  (at level 1,X constr, only parsing): autonaming_scope.


(** It is nicer to write name t than constr:t, see below. *)
Ltac name c := (constr:(c)).


(** * Default fallback renaming strategy

  (Re)defining it now that we have everything we need. *)

Local Open Scope autonaming_scope.
Ltac rename_hyp_default n th ::=
  let res :=
      match th with
      (* | (@eq _ ?x ?y) => name (`_eq` ++ x#n ++ y#n) *)
      (* | Z.le ?A ?B => name (`_Zle` ++ A#n ++ B#n) *)
      | ?x <> ?y => name ( `_neq` ++ x#(decr n) ++ y#(decr n))
      | @cons _ ?x (cons ?y ?l) =>
        match n with
        | S ?n' => name (`_cons` ++ x#n ++ y#n ++ l#n')
        | 0 => name (`_cons` ++ x#n)
        end
      | @cons _ ?x ?l =>
        match n with
        | S ?n' => name (`_cons` ++ x#n ++ l#n')
        | 0 => name (`_cons` ++ x#n)
        end
      | (@Some _ ?x) => name (x#(S n))
      | (@None _) => name (`_None`)
      | _ => fail
      end in
  res.

(* Call this in your own renaming scheme if you want the "hneg" prefix
   on negated properties *)
Ltac rename_hyp_neg n th :=
  match th with
  | ~ (_ = _) => fail 1(* h_neq already dealt by fallback *)
  | ~ ?th' => name (`not` ++ th'#(S n))
  | _ => fail
  end.

Local Close Scope autonaming_scope.

(* Entry point of the renaming code. *)
Ltac fallback_rename_hyp_name th :=
  let depth := rename_depth in
  let $h := constr:(ltac:(let x := default_prefix in exact x)) in
  let l := fallback_rename_hyp depth th in
  match l with
    nil => fail 1
  | _ => let nme := build_name (h::l) in
         fresh nme
  end.

(* Formating Error message *)
Inductive LHMsg t (h:t) := LHMsgC: LHMsg t h.

Notation "h : t" := (LHMsgC t h) (at level 1,only printing, format
"'[ ' $h ':' '/' '[' t ']' ']'").

Ltac rename_hyp_with_name $h th := fail.


(* Tactic renaming hypothesis H. Ignore Type-sorted hyps, fails if no
renaming can be computed. Example of failing type: H:((fun x => True) true). *)
Ltac autorename_strict $h :=
  match type of $h with
  | ?th =>
    match type of th with
    | _ =>
      let l := rename_hyp_with_name $h th in
      let dummy_name := fresh "dummy" in
      rename $h into dummy_name; (* frees current name of H, in case of idempotency *)
      let newname := build_name_no_suffix l in
      rename dummy_name into newname
    | Prop =>
      let dummy_name := fresh "dummy" in
      rename $h into dummy_name; (* frees current name of H, in case of idempotency *)
      let newname := fallback_rename_hyp_name th in
      rename dummy_name into newname
    | Prop =>
      let c := constr:(LHMsgC th H) in
      fail 1 "no renaming pattern for " c (* "no renaming pattern for " $h *)
    | _ => idtac (* not in Prop or "no renaming pattern for " $h *)
    end
  end.

(* Tactic renaming hypothesis H. *)

Ltac autorename $h := try autorename_strict H.

(*
(* Tests *)
Print Visibility.
Local Open Scope autonaming_scope.
Ltac rename_hyp1 n th :=
  match th with
    (* | (?min <= ?x) /\ (?x < ?max) => name (x#n ++ `_bounded_` ++ min#n ++ `_` ++ max#n) *)
  | ((?min <= ?x) /\ (?x <= ?max))%nat => name (x#n ++ `_bounded` ++ min#n ++ max#n)
  end.
(* example of adhoc naming from hyp name: *)
Ltac rename_hyp_with_name $h th ::=
  match reverse goal with
  | H: ?A = $h |- _  =>
    name ( A## ++ `_same`)
    (* let _ := freshable A in *)
    (* name (`same_as` ++ A#1) *)
  end.
Local Close Scope autonaming_scope.

Ltac rename_hyp n th ::=
  match th with
  | _ => rename_hyp1 n th
  end.

Goal forall x1 x3:bool, forall a z e : nat,
      z+e = a
      -> z = a
      -> forall SEP:(True -> True),
        a = z+z
        -> z+z <= a <= e + e
        -> ((fun f => z = e) true)
        -> forall b1 b2 b3 b4: bool,
          True -> True.
Proof.
  intros.
  autorename a.
  autorename H2.
  autorename H1.
  Fail autorename_strict H2.

*)
