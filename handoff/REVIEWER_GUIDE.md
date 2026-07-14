# Specialist reviewer guide

## Review request

Please assess one narrow question:

> Is the proposed proof of the middle-stair conjecture mathematically correct,
> apparently new, and worth developing into a short paper?

The proof is formally verified, but the requested review is not a Lean code
review alone. The main unresolved issue is originality, especially whether the
low-activity density inequality is already known in parallel chip-firing or
fixed-energy sandpile terminology.

## Efficient reading order

1. Read the abstract and Theorem 1.1 in `paper/main.tex` or the compiled PDF.
2. Read Lemma 3.1, the selected-prefix low-activity density bound, in full.
3. Check Lemma 4.1, where the affine complement gives the high-activity bound.
4. Check the short activity-one-half and alternation argument in Section 5.
5. Read `CLAIM_BOUNDARY.md` and `NOVELTY_AND_PRIOR_ART.md`.
6. Use `PROOF_TO_LEAN_MAP.md` only if you want to inspect the formal proof.

## Questions on which feedback is most valuable

- Is it legitimate to choose a different centered-prefix minimum at each
  vertex and then sum the resulting coordinate inequalities?
- For an edge `{v,w}`, is the derivation
  `T K_vw <= 2q < T`, hence integral `K_vw <= 0`, correct with the stated
  cyclic phase convention?
- Does `q<T` suffice to put every coordinate of a returning orbit in the box
  `0 <= sigma(v) <= 2 deg(v)-1`, as required for complementation?
- Does Jiang-Scully-Zhang Theorem 6.2 apply to the cyclic firing words exactly
  as used here, including an arbitrary return length rather than only a least
  period?
- Does balanced nonclumpiness force vertexwise alternation in the claimed way?
- Does the final argument establish least eventual state period, rather than
  only activity or firing-word period?
- Is the low-activity density inequality known under another name or an easy
  corollary of an established potential or rotation-number theorem?
- Is the result best handled as a paper, a short note, or a proof communicated
  to the conjecture authors for incorporation into their work?

## Formal check

From `formal/`:

```powershell
lake -KmaxJobs=1 build
lake env lean AxiomAudit.lean
```

The terminal result is
`MiddleStair.middle_stair_least_eventual_period_two`. The source contains no
`sorry`, `admit`, or project axiom. The axiom report contains only ordinary
Lean/mathlib foundations: `propext`, `Classical.choice`, and `Quot.sound`.

The finite nonclumpiness certificate is kernel-checked, but a human should
still compare its sector and local-state encoding with the published
Jiang-Scully-Zhang argument.

## Scope of the requested response

A useful review can be brief. Please identify:

1. the first invalid or unclear mathematical step, if any;
2. the closest known theorem or terminology for Lemma 3.1;
3. any missing hypothesis or endpoint issue;
4. whether the nonclumpiness dependency is cited and used correctly; and
5. a blunt recommendation: abandon, revise privately, write a short note, or
   prepare a paper.

## Outreach routing

The original request did not unambiguously identify two individual recipients,
so this bundle contains role-based, unsent drafts:

- `EMAIL_DRAFT_CONJECTURE_AUTHOR.md` for one of David Ji, Michael Li, or Daniel
  Wang;
- `EMAIL_DRAFT_NONCLUMPINESS_AUTHOR.md` for one of Tian-Yi Jiang, Ziv Scully,
  or Yan X. Zhang.

Choose one route, personalize it, and verify the recipient's current contact
details independently. No message has been sent.
