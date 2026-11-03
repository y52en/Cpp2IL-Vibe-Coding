# ARM64 recovery checkpoint 4378

This checkpoint advances the upstream-derived implementation from checkpoint 4351 through 4378. It adds conservative parameter identity/address emission, floating comparisons, constrained generic field layouts, by-reference field arguments, Boolean constant phi recovery, null-return phi recovery, guarded widened array indexes, and metadata-bound public class/value property getter recovery. Existing method accessor identities and ambiguity remain protected; no field visibility is widened.

Recorded validation of the frozen candidate: 4,715 full tests passed, zero failed/skipped; 57 focused class-accessor tests passed. The fixed ordered 14,845-method census is unchanged. Relative to 4377, 634 generated method bodies changed, with zero clean-to-diagnostic classification regressions; these are source diagnostics, not native equivalence counts.

The native trial bound 311 previously unmatched methods: 45 failed compilation and 266 reached native comparison. Nine initially matched in the mixed trial, but only one survived filtered rebuilds and all 16 ordinary gates. Independent frozen replay is still in progress, and this publication claims no native adoption for 4378 and no achievement of 90 percent. Earlier formally adopted restoration results remain separate.

The companion JSON pins the frozen archive and the 26 changed production/test C# files. Repository-relative test-data paths in `Cpp2IL.Core.Tests/Paths.cs` are retained from the previous publication. Build outputs, local proof scratch files, game data and binary inputs are not published. Recorded tests apply to the frozen candidate; this source publication does not rerun the full suite. No MetaMikuAI fork changes are imported.
