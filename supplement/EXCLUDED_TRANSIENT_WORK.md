# Excluded follow-up: diamond-tail transients

The source research repository also contains a conventional argument for an
explicit quadratic lower bound on the time required to enter the eventual
two-cycle along a diamond-with-tail graph family.

That work is deliberately excluded from this paper and formal snapshot for
three reasons:

1. It is a distinct transient-complexity question, not needed for the
   middle-stair theorem.
2. The abstract Lean return-time theorem remains conditional on a
   `DiamondTailCertificate`; the concrete graph has been partly formalized but
   no end-to-end certificate instance is present.
3. Prior art for transients restricted to the strict middle band has not
   received the targeted literature review needed for a claim of novelty.

Do not append this material to the first specialist handoff. If pursued, it
should become a separate note after the concrete certificate, literature
review, and a clear comparison with known exponential transient constructions
are complete.
