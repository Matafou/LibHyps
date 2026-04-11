# Changes from 4 to 5.0

## Under the hood: switch to Ltac2

Almost all tactics are now implementd in Ltac2. They are musch faster.

This implies a few changes:

- no more "list" variant of the tactical `; { }`. See below.
- Customization must be written in ltac2, to come back to ltac1
  standard mode you need to do `Local Set Default Proof Mode
  "Classic".`

## Incompatibilities

Things should me mostly forwward compatible except customization that
must be written in Ltac2.

## New features

- With `especialize` subgoals generated from a hypothesis H now
  depends on all premises quantified before H. This is logically more
  sound. This should not introduce incompatibilities buy itself from
  libhyps 4.
- Since libhyps 4 `especialize` now by default quantifies hypothesis
  that are not mentioned instead of declaring evars. To build evars
  instead, use the `with x,y` argument. See README.md.
- new experimental tactic `assert premise i of H` generate a subgoal
  (like assert) for the `i`th premise of H. The asserted subgoal is
  not applied to `H` (but can be used later on to do so). See
  README.md.

## Changes concerning the user customization

### Custom auto naming must now be written in ltac2.

Tranlation from ltac1 is straightforward. Example:

``` coq
Require Import Ltac2.Ltac2.
From Stdlib Require Import List.
Import ListNotations.
Local Set Default Proof Mode "Classic". (* Optional This restores ltac1 proof mode. *)


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
```

### No more "list" variant of the tactical `; { }`.

Ltac2 being much faster, no more need for those variants. Typically
`/g` now is a shotcut for `; { move_up_types }` (`group_up_list`
removed).


## Unplugged syntax

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

