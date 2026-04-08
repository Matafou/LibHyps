# Changes from 4 to 5.0

- Almost all tactics are implementd in Ltac2.
  - consequently they are musch faster
  - also no more "list" variant of the tactical `; { }`. Typically
    `/g` now is a shotcut for `; { move_up_types }` (`group_up_list`
    removed).
  - for auto naming, the user defined naming schemes need to be
    written as ltac2 tactics now, instead of ltac1. Tranlation is
    straightforward. Typically
    
``` coq
Require Import Ltac2.Ltac2.
From Stdlib Require Import List.
Import ListNotations.


Ltac2 rename_hyp_2 _ th :=
  match! th with
  | true <> false => [ String "tNEQf" ]
  | true = false => [ String "tEQf" ]
  end.

Ltac2 Set rename_hyp := rename_hyp_2.

(* Suppose I want to add later another naming rule: *)
Ltac2 rename_hyp_3 n th :=
  match! th with
  | Nat.eqb ?x ?y = true => [ String "Neqb"; Rename x ; Rename y ]
  | true = Nat.eqb ?x ?y => [ String "Neqb" ; Rename x ;  Rename y ]
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_3.

Local Set Default Proof Mode "Classic". (* This restores ltac1 proof mode. *)
```
    
- `especialize` now allows the generated subgoals to use the
  quantified hypothesis. This is logically more sound.
- `especialize` now by default quanttifies hypothesis that are not
  mentioned. To build evars instead, use the `with x,y` argument. See
  README.md.
- `especialize` has a variant where the subgoal are transformed into a
  new hypothesis instead of being directly applied to the initial
  hypothesis. This variant can create only one subgoal.

## Unpoolugged syntax

- `tac1 ;; tac2` a,d `tac1 ;!; tac2` syntax definitely disabled.
  Although you can re-enable it with:
  
``` coq
Tactic Notation (at level 4) tactic4(tac) ";;" tactic4(tach) := then_eachnh tac tach. `
Tactic Notation (at level 4) tactic4(tac) ";!;" tactic4(tach) := (then_eachnh_rev tac tach).
```


# Changes from 1.x to 2.x

## New Syntax

+ The tactical `then_eachnh tac1 tac2` has now syntax `tac1 ; { tac2 }`.
+ The tactical `then_eachnh_rev tac1 tac2` has now syntax `tac1 ; {< tac2 }`.
+ `tac /s` is an alias for `tac ;{ substHyp }`
+ `tac /r` is an alias for `tac ;{ revertHyp }`
+ `tac /n` is an alias for `tac ;{ autorename }`
+ `tac /g` is an alias for `tac ;{ group_up_list }` which is itself
  preferred to `tac ; { move_up_types }` or `tac ;; move_up_types.`
+ Combinations like `tac /s/n/g` are accepted.
+ Some combination have shortcuts, e.g. `tac /sng` stands for `tac
  /s/n/g`. Other shortcuts include `\sn`,`\ng`,`\sg`...

## Old syntax

+ "tac1 ;; tac2" remains, but you can also use "tac1; { tac2 }".
+ "tac1 ;!; tac2" remains, but you can also use "tac1; {< tac2 }".
+ "!tac", "!!tac" etc are now only loaded if you do: 
  `Import LibHyps.LegacyNotations.`, the new following
  composable tacticals are preferred:

## New Tactical for tactical dealing with all hyps at once (OBSOLETE IN > 5.0)

 + "tac1; {! tac2 }" applies tac2 once to *the list of* all new hypothesis.
 + "tac1; {!< tac2 }" applies tac2 once to *the list of* all new hypothesis (reverse order).

Use case: new tactic `group_up_list` is a faster version of
`move_up_types` and deals directly with the list of hypothesis.

Note for developping other such tactics: the list of hypothesis uses
the type `LibHyps.TacNewHyps.DList`.

## `move_up_types` now groups variables with similar types.

Feature wish https://github.com/Matafou/LibHyps/issues/5 by @Yazko:
non-Prop hypothesis with same type are now grouped, which takes
benefit of Coq's goal printing mechanism's own factorization
heuristic.

## `group_up_list` is a (faster) variant of move_up_types

It applies on a list of hyptohesis, so you should use it like this:

```
intros ; {! group_up_list }. 
```

