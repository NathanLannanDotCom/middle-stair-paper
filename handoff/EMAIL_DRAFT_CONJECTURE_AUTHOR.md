# Unsent draft: conjecture author

**Subject:** Private request: candidate proof of Conjecture 2 in parallel chip-firing

Dear [Professor/Dr./First name and surname],

I am writing to ask for a private technical review of a candidate proof of
Conjecture 2 in Ji-Li-Wang, *Non-Stabilizing Parallel Chip-Firing Games*
(arXiv:2408.10508v2).

The proposed theorem is that every nonnegative integral configuration on a
finite connected simple graph with

`2|E|-|V| < |sigma| < 2|E|`

has least eventual state period two. The main step is a graph-independent
density lemma: on a returning orbit, activity below one half implies at most
`2|E|-|V|` chips. It is proved by choosing a minimum of a centered firing-prefix
function independently at each vertex and pairing the resulting integral
correction terms edge by edge. Complementation gives the high-activity bound;
Jiang-Scully-Zhang nonclumpiness then gives alternating firing.

I have attached the paper draft and can share the small, pinned Lean 4
repository that verifies the complete theorem. The Lean check supports
correctness but does not establish novelty. I have made no claim of priority
and have not posted the result publicly.

Could you tell me whether the conjecture remains open to your knowledge,
whether the density lemma is already known in another form, and whether you
see a flaw in the different-time edge-pairing argument? A blunt recommendation
on whether this merits a short note, a fuller paper, or simply communication
to the original authors would be very helpful.

Thank you for considering it.

Best,

Nathan Lannan
nathan@nathanlannan.com
