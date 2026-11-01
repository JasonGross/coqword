# Port of `mathcomp.word` to the standard library's `Zmod`/`bits`

This branch makes `n.-word` the Rocq standard library type
`bits (Z.of_nat n)`, that is `Zmod (2 ^ Z.of_nat n)` from `Stdlib.Zmod`,
and turns the word operations into the `Zmod` operations or thin wrappers
around them. All names and statements of `src/word.v` are kept.
`src/word_ssrZ.v` is unchanged. Built with Rocq 9.2.0, rocq-stdlib 9.1.0
and MathComp 2.6.0 (and with Rocq 9.4+alpha and MathComp master).

## The type

| name | before | now |
|---|---|---|
| `modulus n` | `two_power_nat n` | `(2 ^ Z.of_nat n)%Z`, `simpl never`. `modulusZE : modulus n = 2 ^ n` holds by `reflexivity`; `modulus_two_power_nat : modulus n = two_power_nat n` is new. |
| `word n` | `Record word := mkWord { toword :> Z; _ : isword toword }` | `Definition word : Type := Zmod modulus` (so `word n = bits (Z.of_nat n)` by `wordE`, and by conversion). A definition, not a notation, so that the structure instances are keyed on `word`. |
| `toword` | the record projection, a coercion | `Definition toword (w : word) : Z := Zmod.unsigned w`, `simpl never`, still a coercion `word >-> Z` (`towordE : toword w = Zmod.unsigned w`). |
| `mkWord pf` | the constructor | `Definition mkWord (z : Z) (pf : isword z) : word := Zmod.of_small_Z modulus z`; `towordK : toword (mkWord pf) = z`. |
| `isword z` | notation `(0 <=? z) && (z <? modulus)` | unchanged |
| `mkword z` | `mkWord (mkword_proof z)` (through `zmod_pow2`) | `Zmod.of_Z (modulus n) z`; `mkwordE : mkword z = mkWord (mkword_proof z)`. |
| `word0` | `mkWord isword0` | `Zmod.zero`; `word0E`. |
| `word1` | `mkWord isword1` | `Zmod.one`; `word1E`. |
| subType, eqType, countType | `[isSub for toword]`, `by <:` | an explicit `isSub` instance with `Sub := mkWord`, `Sub_rect := word_rect` (built from `mkWord_toword : mkWord (isword_toword w) = w`), `SubK := towordK`; the `by <:` instances are unchanged. `val`, `valP`, `val_inj`, `val_eqP`, `insubd` work as before. |
| zmodType, comNzRingType | from `ord_of_word` | the laws come from `Zmod.add_comm`, `Zmod.add_assoc`, `Zmod.add_0_l`, `Zmod.add_opp_same_r`, `Zmod.mul_comm`, `Zmod.mul_assoc`, `Zmod.mul_1_l`, `Zmod.mul_add_l`, `Zmod.unsigned_1_pos`. The `ord_of_word`/`word_of_ord`/`zmod_of_word`/`word_of_zmod` maps and their additive and multiplicative instances are kept. |

## Operations

| name | before | now | bridge |
|---|---|---|---|
| `add_word`, `sub_word`, `opp_word`, `mul_word` | `mkword (urepr w1 + urepr w2)` and so on | `Zmod.add`, `Zmod.sub`, `Zmod.opp`, `Zmod.mul` (definitions, width implicit) | `add_word_mkword`, `sub_word_mkword`, `opp_word_mkword`, `mul_word_mkword` give the old form |
| `wand`, `wor`, `wxor` | `mkWord (wand_subproof w1 w2)` | `Zmod.and`, `Zmod.or`, `Zmod.xor` | `wandE_mkWord`, `worE_mkWord`, `wxorE_mkWord`; `toword_wand`, `toword_wor`, `toword_wxor` (`urepr_wand` and friends are kept) |
| `lsr w k` | `mkWord (lsr_proof w k)` (through `shiftr_nat`) | `Zmod.sru w (Z.of_nat k)` | `lsrE_mkWord`; `urepr_lsr` kept |
| `lsl w k` | `mkword (Z.shiftl (urepr w) (Z.of_nat k))` | unchanged; equal to `Zmod.slu w (Z.of_nat k)` by `reflexivity` | `lsl_slu` |
| `asr w k` | `mkword (Z.shiftr (srepr w) (Z.of_nat k))` | unchanged (`srepr` is not syntactically `Zmod.signed`) | - |
| `srepr`, `wsplit`, `wumul`, `wumul2`, `wsmul`, `w0extend`, `rotl`, `rotr`, `subword`, `wcat`, `t2w`, `w2t`, `wbit`, `wsize` | | unchanged definitions (`mkWord`/`mkword` based) | - |

The wrapped operations are plain definitions, not abbreviations, so
`@add_word n` keeps the width as its implicit argument and the HB instances
stay keyed on `word`. `add_word w1 w2` and `Zmod.add w1 w2` are convertible,
and `rewrite /add_word` exposes the stdlib term.

## What does not stay compatible

1. `mkWord` is a function, not a constructor. `case: w => [z hz]` on a word
   gives the `Zmod` record fields (`z : Z` and a `Bool.Is_true` proof whose
   type mentions the private `small`), not `hz : isword z`. Use
   `case/word_rect: w => z hz` (or `elim/word_rect`), or `have hz := isword_word w`.
   `match w with mkWord z hz => ...` in a definition does not work; use
   `toword w` and `isword_word w`.
2. Equations that held by conversion are now lemmas:
   `toword (mkword z) = z mod modulus n` (`mkwordK`, `mkword_valK`),
   `toword (mkWord pf) = z` (`towordK`), `urepr (add_word w1 w2) = ...`
   (`addwE`), `toword word0 = 0` (`toword0`, `toword_zero`, `urepr0`,
   `urepr_zero`), `toword word1 = 1` (`toword1`, `toword_one`, `urepr1`,
   `urepr_one`), `urepr (wand w1 w2) = Z.land ...` (`urepr_wand`),
   `urepr (lsr w k) = Z.shiftr ...` (`urepr_lsr`), `toword (t2w t) = t2w_def t`
   (`towordK`). `by []`, `done`, `/=` and `exact: erefl` that relied on them
   need a `rewrite` first. For closed widths (`8.-word`) and closed values
   they still compute with `vm_compute`/`cbv`.
3. `rewrite /modulus two_power_nat_equiv` becomes `rewrite /modulus` (or
   `modulus_two_power_nat`). `modulus n` no longer computes by `simpl`
   (it is `simpl never`) and `0 <= modulus n` is no longer closed by `done`
   for a symbolic `n` (it was, because `two_power_nat n` is a `Zpos`);
   `modulus_gt0`, `modulus_gt0Z` are there.
4. The coercion `toword : word >-> Z` applies to a term whose type is
   syntactically `word n`. For a term whose type is a structure sort, such as
   `s`_i` with `s : seq n.-word` (its type is `GRing.Zmodule.sort _`), Rocq
   unfolds the type past `word` to `Zmod` to look for a coercion, and finds
   none. Write `(s`_i : n.-word)` or `urepr s`_i`. (With the record type the
   unfolding stopped at `word`.) Two statements in `word.v` needed this
   (`wcat_wbitE`, `wcatE`).
5. Because `add_word w1 w2`, `mkword z`, `word0`, ... are convertible to the
   `Zmod` terms, `rewrite` with a `Zmod` lemma or with `mkwordK` can match
   more subterms than before (for example `rewrite towordK` also rewrites
   `toword word0`, since `word0 = Zmod.zero` unfolds to `of_small_Z _ 0`).
6. `simpl`/`cbn` on `toword (mkword z)` no longer gives `zmod_pow2 z n`;
   `toword` is `simpl never` (unfolding it gives the stdlib
   `if small z m then z else 0` guard). Use `mkword_valK`.
7. Compile time of `word.v`: 16 s instead of 8 s on the same machine
   (Rocq 9.2, MathComp 2.6).

## New lemmas

`wordE`, `towordE`, `modulus_gt0Z`, `modulus_two_power_nat`,
`modulusS_ge2`, `isword_toword`, `towordK`, `toword_inj`, `mkWord_toword`,
`word_rect`, `word_rec`, `word_ind`, `mkwordE`, `toword0`, `urepr0`,
`word0E`, `toword1`, `urepr1`, `word1E`, `toword_zero`, `urepr_zero`,
`toword_one`, `urepr_one`, `add_word_mkword`, `sub_word_mkword`,
`opp_word_mkword`, `mul_word_mkword`, `toword_wand`, `toword_wor`,
`toword_wxor`, `wandE_mkWord`, `worE_mkWord`, `wxorE_mkWord`, `lsl_slu`,
`lsrE_mkWord`.
