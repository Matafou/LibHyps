
# Changes from 1.x to 2.x

## New Syntax

  + "tac1 ;; tac2" remains, but you can also use "tac1; { tac2 }".
  + "tac1 ;!; tac2" remains, but you can also use "tac1; {< tac2 }".

  + "!tac", "!!tac" etc are now only loaded if you do: 
    `Import LibHyps.LegacyNotations.`, the new following
    composable tacticals are preferred:

  + `tac /s` is an alias for `tac ;{ substHyp }`
  + `tac /r` is an alias for `tac ;{ revertHyp }`
  + `tac /n` is an alias for `tac ;{ autorename }`
  + `tac /g` is an alias for `tac ;{ group_up_list}` which is itself
    preferred to `tac ; { move_up_types }` or `tac ;; move_up_types.`

  + Combinations like `tac /s/n/g` are accepted.
  + Some combination have shortcuts, e.g. `tac /sng` stands for `tac
    /s/n/g`. Other shortcuts include `\sn`,`\ng`,`\sg`...

## New Tactical for tactical dealing with all hyps at once

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

