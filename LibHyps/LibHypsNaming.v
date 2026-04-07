(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)
(* **************************************************************** *)

(** This file defines a tactic "autorename h" (and "autorename_strict
    h") that automatically rename hypothesis h following a systematic,
    but customizable heuristic.

    Comments welcome. *)

Require Import Arith ZArith List.
Require LibHyps.TacNewHyps.

(* Import ListNotations. *)
(* Local Open Scope list. *)
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
Local Set Default Proof Mode "Classic".
(* Require Import LibHyps.LibHypsDebug. *)

Local Ltac2 backtrack (msg:string) := Control.zero (Tactic_failure (Some (fprintf "Backtrack: %s" msg))).
Local Ltac2 control_try tac := Control.plus tac (fun _ => ()). 

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
Require Import ZArith.

Ltac2 decr (n:int):int :=
  if Int.equal n 0 then 0 else Int.sub n 1.

Ltac2 incr (n:int):int := Int.add n 1.

Ltac2 Type rename_directive := [ String(string) | Rename(constr) | RenameN(int,constr) ].
Ltac2 Type rename_directives := rename_directive list.

(* For debugging *)
Module Debug.
Ltac2 pr_directive () (d:rename_directive) :=
  match d with
    String s => fprintf "%s" s
  | Rename c => fprintf "%t" c
  | RenameN i c => fprintf "N(%i,%t)" i c
  end.
End Debug.
Ltac2 Type hypnames := string list.

(** This determines the depth of the recursive analysis of a type to
    compute the corresponding hypothesis name. generally 2 or 3 is
    enough. More gives too log names, less may give identical names
    too often. *)
Ltac2 mutable rename_depth := 3.
(* The pretty printing of numerical values is by default 1, 2... Set this to
   true (Ltac2 Set numerical_sufs := true) to have 1z, 1n or 1N depending of the type nat, Z or N. *)  
Ltac2 mutable numerical_sufx := false.
(* Whether autorename should add a "_" at the end of every hypothesis name *)
Ltac2 mutable add_suffix := true.
(* Whether autornename should add "h_" at the beginniong of each hypothesis name *)
Ltac2 mutable add_prefix := true.

(** Default prefix for hypothesis names. *)
Ltac2 default_prefix():string := "h".

(** A few special default chunks, for special cases in the naming heuristic. *)
Ltac2 impl_prefix() := "impl".
Ltac2 forall_prefix() := "all".
Ltac2 exists_prefix() := "ex".

(** ** The custom renaming tactic
    
  This is the customizable naming tactic that the user should REDEFINE along
  his development. See below for an example of such redefinition. It should
  always fail when no name suggestion is found, to give a chance to the
  default naming scheme to apply. *)
#[warnings="-ltac2-unused-variable"] 
Ltac2 mutable rename_hyp (stop:int)  (th:constr): rename_directives := backtrack "rename_hyp".


(*  Typical use, in increasing order of complexity, approximatively
  equivalent to the decreasing order of interest. *)
(**
<<
From Stdlib Require Import  Sorting.SetoidList.
Ltac2 rename_hyp_2 n th :=
  match! th with
  | true <> false => [String "tNEQf"]
  | true = false => [String "tEQf"]
end.
Ltac2 rename_hyp_3 n th :=
  match! th with
  | List.In ?e ?l => [String "lst_in" ; RecRename n e ; RecRename  0 l]
  | InA _ ?e ?l => [String "inA" ; RecRename n e ; RecRename 0 l ]
  | @StronglySorted _ ?ord ?l =>  [ String"strgSorted" ; RecRename (Int.add 2 n) l]
  | @Forall _ ?p ?x => [String "lst_forall" ; RecRename n p ; RecRename n x]
  | @Forall2 _ _ ?p ?x ?y => [String "_lst_forall2" ; RecRename n p ; RecRename n x; RecRename n y]
  | NoDupA _ ?l => [String "_NoDupA" ; RecRename n l ]
  | NoDup _ ?l => [String "_NoDup" ; RecRename n l ]
  | _ => rename_hyp_2 n th
  end.
Ltac2 Set rename_hyp := rename_hyp_3.
>> *)

(* This one is similar but for internal use *)
#[warnings="-ltac2-unused-variable"] 
Ltac2 mutable rename_hyp_default (n:int) (th:constr): rename_directives := backtrack "rename_hyp_default".

Module Ltac2.

(* from [ "foo" ; "bar" ; "oof" ] to "h_oof_bar_foo_". Note the reversing of the list *)
Ltac2 build_name_gen (sep:string) (prefx:bool) (suffx:bool) (l:string list) :=
  let l := if prefx then (default_prefix()::l) else l in
  (String.app (String.concat sep l) (if suffx then "_" else "")).

Ltac2 build_name (l:string list): string := build_name_gen "_" add_prefix add_suffix (List.rev l).

Ltac2 string_of_int (i:int) := Message.to_string (Message.of_int i).



Ltac2 string_forall (p:char -> bool) (s:string) : bool :=
  let rec check i :=
    if Int.ge i (String.length s) then true
    else if p (String.get s i) then check (Int.add 1 i) else false
    in
  check 0.


Ltac2 codepercent():int := (Char.to_int (String.get "%" 0)).
Ltac2 code0() := Char.to_int (String.get "0" 0).
Ltac2 code9() := Char.to_int (String.get "9" 0).

Ltac2 is_digit (c:char): bool :=
  let code := Char.to_int c in
  Bool.and (Int.le (code0()) code) (Int.le code (code9())).

Ltac2 string_first (p:char -> bool) (s:string) : int :=
  let lgth := String.length s in
  let rec count i :=
    if Int.ge i lgth then i
    else if p (String.get s i) then i
         else count (Int.add 1 i)
  in
  count 0.

Ltac2 Eval (string_first (fun c => Int.equal (Char.to_int c) (codepercent())) "xxxcc").

Ltac2 string_shorten_percent (s:string) : string :=
  let i := string_first (fun c => Int.equal (Char.to_int c) (codepercent())) s in
  String.sub s 0 i.

  
(** Generate fresh name for numerical constants.

   Warning: problem here: hyps names may end with a digit: Coq may
   *replace* the digit in case of name clash. If you are bitten by
   this, you should switch to "Ltac add_suffix ::= constr:(true)." so
   that every hyp name ends with "_", so that coq never mangle with
   the digits *)

(* FIXME: this relies on printf to build a string from a constr in
   nat, Z and N. It feels wrong. *)
Ltac2 build_numerical_name (t:constr):string :=
  let s := Message.to_string (fprintf "%t" t) in
  let s := string_shorten_percent s in (* remove trailing "%scope" *)
  if string_forall is_digit s
  then if Bool.neg numerical_sufx then s
       else 
         let typ := Constr.type t in
         match! typ with
         | Z => String.app s "z"
         | nat => String.app s "n"
         | N => String.app s "N"
         end
       else backtrack "numerical_names_nosufx".


(* FIXME: find something better to detect implicits!! *)
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



Ltac2 arobase():char := (Char.of_int 64).


(** Build a chunk from a simple term: either a number or a freshable
   term. *)
Ltac2 box_name t : string :=
  (* Hackish? *)
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
          (* printf "<infomsg>IND: %t</infomsg>" t; *)
          let s:string := Message.to_string (fprintf "%t" t) in
          let s := if Char.equal (String.get s 0) (arobase())
                   then String.sub s 1 (Int.sub (String.length s) 1)
                   else  s in
          s
      | _ => build_numerical_name t
      end
  end.

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
   ignored as implicits. *)
Ltac2 rec rename_app (nonimpl:int) (stop:int) (acc:string list ref) th: unit :=
  Control.once_plus (fun () => let s := box_name th in
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
    let _newstop := Int.sub stop 1 in
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
           let _ := in_context nme typ tac_under_binder in
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
           let _ := in_context nme typ tac_under_binder in
           ()

        else
          (Ref.set acc (impl_prefix() :: Ref.get acc);
           rename_hyp_chained_quantifs newstop acc subth)
    | App f args =>
        match Unsafe.kind f, Unsafe.kind constr:(@Init.Logic.ex) with
        | Ind ind _, Ind ind' _ =>
            if Ind.equal ind ind'
            then (
                Ref.set acc ((*Ident.to_string a ::*) exists_prefix() :: Ref.get acc);
                  match Unsafe.kind (Array.get args 1) with
                  | Lambda _bnd subth => rename_hyp_chained_quantifs newstop acc subth
                  | _ => backtrack "not exist"
                  end)
            else backtrack "not exist"
        | _ => backtrack "not exist"
        end
    | _ => backtrack "no quantif"
    end


with fallback_rename_hyp_specials stop (acc:string list ref) th :unit :=
    let newstop := Int.sub stop 1 in
    let freeze := Ref.get acc in
    Control.once_plus 
       (* First see if user has something that applies *)
       (fun() => let dirs := rename_hyp newstop th in
                 interp_directives newstop acc (List.rev dirs) )
       (* if it fails try default specials *)
       (fun _ => let dirs := rename_hyp_default newstop th in
                  Ref.set acc freeze; (* backtracking acc by hand here *)
                  interp_directives newstop acc (List.rev dirs))

with fallback_rename_hyp stop (acc:string list ref) th:unit :=
          if Int.le stop 0 then ()
          else
            Control.once_plus (fun () => fallback_rename_hyp_specials stop acc th)
              (fun _ =>
                 lazy_match! th with
                 | forall _, _ => fallback_rename_hyp_quantif stop acc th
                 | exists _, _ => fallback_rename_hyp_quantif stop acc th
                 | _ => let numnonimpl := count_impl th in
                        let _ := rename_app numnonimpl stop acc th in
                        ()
                 end)

with interp_directives stop acc ld:unit :=
  List.fold_right (fun d _ => interp_directive stop acc d) ld ()

with interp_directive stop acc d :=
    (* printf "<infomsg>interp_directive %a %a</infomsg>" pr_acc (Ref.get acc) pr_directive d; *)
  match d with
  | String s => Ref.set acc (s :: (Ref.get acc))
  | Rename t => fallback_rename_hyp stop acc t
  | RenameN n t => fallback_rename_hyp n acc t
  end.

(* Like in_context but then forget about the new goal. Only side effects are
   kept *)
Ltac2 in_context_then_forget nme typ f :=
  Control.once_plus
    (fun () => let _ := in_context nme typ f in backtrack "forget in_context subgoal")
    (fun _ => ()).

Ltac2 rename_acc n th :=
  let acc := Ref.ref [] in
  (* We intentionally create a separate goal and backtrack it at the end. We
     only keep the name stored in acc. *)
  let dummy_nme := Option.get (Ident.of_string "DUMMY_SUBGOAL") in
  in_context_then_forget dummy_nme constr:(Prop) (fun () => fallback_rename_hyp n acc th);
  Ref.get acc.

Ltac2 fallback_rename_hyp_name th: ident :=
  let depth := rename_depth in
  let l := rename_acc depth th in
  (* printf "<infomsg>ICI10 : %a</infomsg>" pr_acc l; *)
  match l with
    [] => backtrack "No name built"
  | _ => let nme := build_name l in
         let id := Option.get (Ident.of_string nme) in
         Fresh.in_goal id
  end.

(* This entry point is for really adhoc user renaming that need to inspect the
goal in depth. For instance itf the name of a variable depends on the presence
of some hypothesis. Currently unplugged.*)
#[warnings="-ltac2-unused-variable"] 
Ltac2 rename_hyp_with_name h th := fail.

(* Tactic renaming hypothesis H. Ignore Type-sorted hyps, fails if no
renaming can be computed. Example of failing type: H:((fun x => True) true). *)
#[global]
Ltac2 autorename_strict (h:ident) :=
  let th := Constr.type (Control.hyp h) in
  let tth := Constr.type th in
  (* printf "<infomsg>th = %t</infomsg>" tth ; *)
  lazy_match! tth with
  (* TODO: the deep entry point *)
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
  | _ =>
      if Constr.equal constr:(Prop) tth
      then  let msg := fprintf "no renaming pattern for %I : %t" h th in
            backtrack (Message.to_string msg)
      else () (* not in Prop or "no renaming pattern for " $h *)
  end.

(* Tactic renaming hypothesis H. *)

Local Ltac2 ltac2_autorename (h:ident) :=
  control_try (fun () => autorename_strict h).

Ltac2 ltac1_autorename (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  ltac2_autorename h.

Ltac2 ltac1_autorename_strict (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  autorename_strict h.

Ltac2 rename_list l acc s :=
  List.iter (fun (n,t) => fallback_rename_hyp n acc t) l;
  Ref.set acc (s :: (Ref.get acc)).

End Ltac2.

(* This is the default renaming hard-coded in LibHYps *)
Ltac2 Set rename_hyp_default :=
  fun n th =>
    if Int.lt n 0 then []
    else
      lazy_match! th with
      | ?x <> ?y => [ String "neq" ; Rename x ; Rename y ] 
      | (@Some _ ?x) =>  [RenameN (incr n) x]
      | (@None _) => [String "None"]
      end.

(* This may be due to the definition of ltac1_autorename which uses
   Ltac1.to_ident, but this is the only way I found to have
   "autorename h" be callable from ltac1: make it a notation expecting
   an ident, and then define a tactic using this notation. If I define
   directly the tatic autorename instead of a notation, then it does
   not accept "autorename id". *)
(* to reproduce:
Ltac2 ltac1_autorename (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  ltac2_autorename h.

Global Ltac autorename h :=
  let tac := ltac2:(h |- Ltac2.ltac1_autorename h) in
  tac h.

Goal 1 = 2 -> False.
Proof.
  intros H. 
  autorename H. (* Ltac1.to_ident fails with Ltac2 exception: No_value *)

More generally to reproduce:

Ltac2 ltac2_mytac (id:ident) := printf "<infomsg>%I</infomsg>" id.

Ltac2 ltac1_mytac (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  ltac2_mytac h.

Global Ltac mytac h :=
  let tac := ltac2:(h |- ltac1_mytac h) in
  tac h.

Local Set Default Proof Mode "Classic".

Goal 1 = 2 -> False.
Proof.
  intros H. 
  Fail mytac H. (* Ltac1.to_ident fails with Ltac2 exception: No_value *)
Abort.

(* Solution *)
Tactic Notation "XXXmytac" hyp(h) :=
  let tac := ltac2:(h |- ltac1_mytac h) in
  tac h.

Ltac mytac' h := XXXmytac h.


Goal 1 = 2 -> False.
Proof.
  intros H. 
  mytac' H. 

*)


Local Tactic Notation "Lautorename" hyp(h) :=
  let tac := ltac2:(h |- Ltac2.ltac1_autorename h) in
  tac h.

Global Ltac autorename h := Lautorename h.

Local Tactic Notation "Lautorename_strict" hyp(h) :=
  let tac := ltac2:(h |- Ltac2.ltac1_autorename_strict h) in
  tac h.
Global Ltac autorename_strict h := Lautorename_strict h.

(*
(* ********** EXAMPLE CUSTOMIZATION ********** *)

(* TESTS *)

(* This settings should reproduce the naming scheme of libhypps-1.0.0
   and libhypps-1.0.1. *)
Ltac2 Set add_suffix := false.
Ltac2 Set numerical_sufx := true.

(* This should maybe be by default *)
Ltac2 rename_hyp_1 n th :=
    if Int.lt n 0 then []
    else
      lazy_match! th with
      | @cons _ ?x (cons ?y ?l) => [String "cons"; Rename x; Rename y; RenameN (decr (decr n)) l]
      | @cons _ ?x ?l => if Int.ge n 1 then [String "cons"; Rename x; RenameN (decr n) l] else [String "cons"]
      end.

(* From there this is LibHypTest from 1f7a1ed2289e439c291fcbd06c51705547feef1e *)
Ltac2 rename_hyp_2 n th :=
  match! th with
  | true <> false => [String "tNEQf"]
  | true = false => [String "tEQf"]
  |  _ => rename_hyp_1 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_2.

(* Suppose I want to add later another naming rule: *)
Ltac2 rename_hyp_3 n th :=
  match! th with
  | Nat.eqb ?x ?y = true => [String "Neqb" ; Rename x ; Rename y]
  | true = Nat.eqb ?x ?y => [String "Neqb" ; Rename x ; Rename y]
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_3.

Ltac2 Set rename_depth := 3.
Import TacNewHyps.Notations.
Close Scope Z_scope.
Open Scope nat_scope.

Lemma dummy: forall x y,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
    Some x = Some y ->
    0 = 1 ->
    223 = 426 ->
    (0 = 1)%Z ->
    x <> y ->
    Nat.eqb (x + 1) 0 <> Nat.eqb 1 y ->
    true = Nat.eqb 3 4  ->
    Nat.eqb (x + 3) 4 = true  ->
    Nat.eqb (2 * (x + 3)) 4 = true  ->
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
Proof.
  intros x y H.
  autorename H.
  Undo 2.
  intros;{ autorename }.

  match type of x with nat => idtac | _ => fail "test failed!" end.
  match type of y with nat => idtac | _ => fail "test failed!" end.
  match type of h_le_0n_1n with 0 <= 1 => idtac | _ => fail "test failed!" end.
  match type of h_le_0z_1z with (0 <= 1)%Z => idtac | _ => fail "test failed!" end.
  match type of h_le_x_y with x <= y => idtac | _ => fail "test failed!" end.
  match type of h_eq_x_y with x = y => idtac | _ => fail "test failed!" end.
  match type of h_eq_223n_426n with 223 = 426 => idtac | _ => fail "test failed!" end.
  match type of h_eq_0n_1n with 0 = 1 => idtac | _ => fail "test failed!" end.
  match type of h_eq_0z_1z with 0%Z = 1%Z => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_3n_4n with true = (3 =? 4) => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_add_x_3n_4n with (x + 3 =? 4) = true => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_mul_2n_add_4n with (2 * (x + 3) =? 4) = true => idtac | _ => fail "test failed!" end.
  match type of h_eq_true_leb_3n_4n with true = (3 <=? 4) => idtac | _ => fail "test failed!" end.
  match type of h_eq_1n_0n with 1 = 0 => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y0 with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_neq_eqb_add_0n_eqb_1n_y with  (x + 1 =? 0) <> (1 =? y) => idtac | _ => fail "test failed!" end.
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





(* Ltac autorename h := *)
  (* let tac := ltac2:(h |- ltac2_autorename h) in *)
  (* tac h. *)

  (* Unset Printing Notations. *)

(* Ltac2 Eval (count_impl constr:(3 + 4)). *)

Import TacNewHyps.Notations.
Parameters X Y: nat -> Prop.
Parameters PX: X 3.
Parameters PY: Y 3.

Local Ltac rename_or_revert H := autorename_strict H + (try revert H).

Goal forall [A : Type] (P Q : A -> Prop) (x : A), P x -> Q x -> (exists2 x : A, P x & Q x) -> ((fun x => x = x) 1) -> ex2 P Q -> False.

  intros A P Q x H H0 H1 HH H2.

  autorename H1.
  autorename H2.
  autorename H.
  autorename H0.
  Fail autorename_strict HH.
  rename_or_revert HH.
  intros ; { rename_or_revert }.
  Fail intros ; { autorename_strict }.
  

  ltac2:(let l := Ltac2.rename_acc 3 constr:(exists2 x0 : A, P x0 & Q x0) in
         printf "<infomsg>BEFORE BUILDNAME %a </infomsg>" (pr_list pr_string) l;
         let nme := Ltac2.build_name l in
         printf "%s" nme).

  ltac2:(let l := Ltac2.rename_acc 9 constr:(ex2 P Q) in
         printf "<infomsg>BEFORE BUILDNAME %a </infomsg>" (pr_list pr_string) l;
         let nme := Ltac2.build_name l in
         printf "%s" nme).
Abort.

Definition foo := (fun a b:bool => a = b).

Goal forall n m p : nat, forall b:bool, n<m -> m<= p -> True .
Proof.
  intros n m p b H H0.

  assert (forall z, foo b z).
  2:{ } 

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
