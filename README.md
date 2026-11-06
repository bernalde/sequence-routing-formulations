> Current local stage: Completed local compilation, every selected axiom census and genuine sandboxed Comparator with Lean, NanoDa and con-ron passed. Independent bounded source/package review returned SATISFACTORY with no mandatory mathematical or mechanical finding. Exact receipts, review hashes, warnings, cache/resource/runtime/usage limits and unchanged proof/compiler inputs are in VERIFICATION.json. Independent documentary-delta closure and exact software-only export are recorded separately by the coordinator. New public commit/release, hosted preflight, service submission/review and registration have not occurred.

Current source-level successor: the two selected finite-index proofs have explicit named theorem commands and are referenced by their parent Fin abbreviations. Exact prior checks/reviews remain historical to the prior bytes; VERIFICATION.json controls current gates. Remote rendering and public actions have not been performed for this successor.

# Finite sequence routing: routes, costs, and continuous timing

This Lean 4.35 package exposes a qualified mathematical interpretation of the sequence-based routing formulation in Chapter 10 of David E. Bernal Neira's 2021 thesis, based on the joint paper *Formulating and solving routing problems on quantum computers*. It connects the literal binary rows to padded elementary customer routes, preserves the transition objective, and identifies exactly when the continuous timing rows have a solution for a fixed encoded route family.

This locally verified package copies its ten accepted proof modules without modification. The independent Challenge and seven source-theorem aliases compiled and passed actual transitive-axiom checks and genuine sandboxed Comparator with Lean, NanoDa and con-ron. Three finite-index proof dependencies are explicitly compared by proposition and kernel-checked as supporting targets. Independent source-first package review assessed the scope and this comparison boundary. No public repository, hosted preflight, Palomar submission or registration is claimed for this package.

## Mathematical model

There are `n` customers, `v` vehicle slots, and `P = k+2` sequence positions. `none` denotes the depot and `some i` customer `i`. `Data` exposes allowed arcs, real costs/travel times and real customer windows; its load fields are retained but no load-capacity theorem is advertised here.

`Literal D x` contains the actual source rows: zero/one variables, exactly one occurrence of each customer across all vehicles and positions, exactly one node per position, forbidden-arc products, absorbing-depot products after the initial position, and the fixed initial/final/impossible coordinates. `SlotStructure` expresses these conditions for a chosen node in every vehicle-position slot. `encode` gives the one-hot real array; `decode` removes the initial depot and depot padding while retaining customer order.

The ordinary arc-cost objective is the complete nested source sum. `edgeCostFrom` is the cost of a customer list including the initial departure and final depot return. The reverse constructor `padSlots` inserts the customer lists between the initial depot and enough depot entries to reach exactly `k+2` positions.

For timing, `customerRHS` and `returnRHS` retain every nested source term. `LiteralTiming` states their lower bounds and the customer windows. `ScheduleFrom` instead gives a clock for each position along a customer list, with travel lower bounds and waiting allowed. The earliest recurrence takes the maximum of a customer's opening time and predecessor time plus travel; `EarliestWithin` checks its closing bounds.

## Recorded theorem family

The Comparator configuration selects seven endpoints in `Chapter10.Sequence`:

| Endpoint, prefixed `palomar_` | Exact result and qualification |
| --- | --- |
| `literal_iff_decoded` | The complete binary source rows hold iff the real array is the encoding of slots satisfying `SlotStructure`. |
| `literal_decodes_elementary_paths` | A literal feasible array supplies encoded slots whose decoded routes have no repeated customer, length at most `k`, and allowed consecutive edges including the depot return. |
| `bounded_traces_encode` | Customer lists of length at most `k`, covering every customer exactly once and using allowed edges, encode back to literal rows and decode to the original lists. Depot-to-depot travel must be allowed; depot-loop cost is zero for the asserted objective identity. |
| `decoded_cost` | For slots satisfying `SlotStructure`, the nested source objective equals the sum of decoded route costs when depot-loop cost is zero. |
| `literal_timing_iff_schedules` | For fixed slots and clocks, the literal timing rows hold iff each decoded route has its corresponding position schedule, assuming depot clock zero and depot-loop travel time zero. |
| `literal_timing_exists_iff` | For fixed slots satisfying `SlotStructure` and zero depot-loop travel time, there exists a shared customer clock and vehicle-return assignment with depot clock zero iff every decoded route's earliest recurrence satisfies all closing bounds. |
| `literal_duration_minimum` | Under those slot/zero-loop-time hypotheses and earliest-window feasibility, the earliest return vector is attained and its sum is no greater than that of every feasible shared-clock/return assignment. |

These are related interfaces of one mathematical development, not seven independent research contributions. The source proof route uses one-hot decoding, explicit depot padding and literal nested sums; timing existence assembles a shared clock from the globally unique customer occurrences. The final duration statement minimizes return variables for the fixed route family. It is not a theorem that every feasible return variable is tight or that the route family minimizes duration globally.

## Exact scope and boundary cases

- All finite `n`, `v`, and `k`, including zero, remain quantified. `k=0` means two depot endpoint positions and no customer stops. Empty vehicle traces are allowed; a nonempty customer set need not admit a feasible encoding.
- Reverse encoding explicitly assumes exact-once global customer coverage and allowed edges. It does not infer coverage from disjointness or from vehicle labels.
- Depot-loop cost and travel-time conditions are separate. The cost statements require `D.cost none none = 0`. Timing interpretation fixes the depot clock to zero and requires `D.travel none none = 0` to remove all padding contributions. Forward decoding itself does not require either zero-loop hypothesis.
- Travel and cost data are real. No nonnegativity premise absent from the accepted theorem is silently added. Under physical nonnegative travel, the intended schedules inherit the ordinary physical interpretation; that additional consequence is outside this selected family.
- No additional finite depot return window is imposed. Customer opening/closing windows and a return lower bound are exactly those in `ScheduleFrom`.
- The package does not certify vehicle load-capacity constraints, arc-based/grid formulations, route-column completeness, conservative-pruning preservation of a physical optimum, a solver's implementation, global route optimization, ADMM/SCP convergence, or quantum-device/numerical claims.
- No optimization oracle, external solver assumption or numerical test supports these statements. The chosen source proofs use the disclosed ordinary Lean foundations; actual transitive-axiom inspection of all main and auxiliary targets passed.

For an informal nonvacuity check, take one customer, one vehicle, `k=1`, all arcs allowed, zero travel and costs, window `[0,1]`, and the route containing that customer. Its positions are depot/customer/depot and its zero schedule satisfies the displayed definitions. With no customers, idle padded vehicles give another boundary example. These illustrations have not yet been compiled as new package controls.

## Source correspondence, build and review

The source locations are the thesis sequence formulation and continuous-time sequence formulation, particularly the exact binary rows, nested timing sums and fixed-route duration discussion. The package is a qualified adaptation with explicit padding and depot conditions. It makes no blanket certification of all assertions in the thesis or published paper, and it does not assert source-author endorsement.

`SOURCE-MANIFEST.json` records the ten unchanged source files, their SHA-256 hashes, the copied definition fragments and each selected theorem's source endpoint. The complete source-import closure is included; additional Chapter 2 and finite-incidence results remain unselected dependency material rather than advertised package claims. Upstream Mathlib sources are not vendored. Lean and every Lake dependency remain pinned.

With the pinned toolchain installed, normal local checks are:

```sh
lake build
lake env lean AxiomAudit.lean
lake comparator --config comparator.json
```

These checks have passed at the exact inputs in VERIFICATION.json, with the toolchain's bundled independent kernels configured and recorded. All ten compared targets have only the allowed standard foundational axioms. New project outputs were compiled during this task; final checks reused exact unchanged outputs and pinned upstream cache objects. Palomar additionally requires its own full reusable hosted mechanical preflight; a local command is not a substitute. `Challenge.lean` deliberately leaves seven theorem obligations unproved for comparison. `Solution.lean` never imports Challenge and invokes the existing source proofs through aliases.

David E. Bernal Neira is the responsible formalization author and maintainer. AI assistance, the inherited review scope, and actual bounded local package checks are disclosed in `formalization.yaml`. Complete attributable model-token/cost/billing figures are unknown.

The project-owned proof code, build metadata and accompanying software documentation use Apache-2.0. See `LICENSE` and `NOTICE.md`. Source articles, the thesis, publisher material and private audit records are cited rather than redistributed. Dependencies retain their own licenses.

## References

- David E. Bernal Neira, *Modern computational approaches to nonlinear discrete optimization and applications in process systems engineering*, Ph.D. thesis, Carnegie Mellon University, 2021, Chapter 10.
- Stuart Harwood, Claudio Gambella, Dimitar Trenev, Andrea Simonetto, David Bernal and Donny Greenberg, *Formulating and solving routing problems on quantum computers*, IEEE Transactions on Quantum Engineering 2, article 3100117, 2021. [DOI: 10.1109/TQE.2021.3049230](https://doi.org/10.1109/TQE.2021.3049230).

## Auxiliary proof comparison and exact source fidelity

The seven mathematical interfaces above retain their original full hypotheses
and conclusions, including the specific canonical `padSlots` reverse constructor.
All ten accepted source modules remain byte-identical. In the independent
Challenge, `padSlots` explicitly proves/names the source compiler's `_proof_2`
list-index interface so that its computational constructor is structurally equal.

The Comparator additionally records three proof-valued targets:
`Chapter10.Sequence.padSlots._proof_2`,
`Chapter10.Sequence.penultimate._proof_2`, and
`Chapter10.Sequence.second._proof_2`. They establish valid list/finite-position
indices. They are support checks, not three further research contributions.
Their exact propositions must match, while their completed proofs may differ;
this explicitly changes the comparison boundary from proof-body byte identity
for these dependencies to the normal theorem-target type/proof check. Every
computational definition still undergoes structural comparison. No definition
body exemption, custom axiom, disabled sandbox or skipped kernel is used.

The local checks used an enforced 12 GiB memory cap, zero swap and two CPUs.
Earlier preparation and failed attempts remain private evidence. The manual
pinned hosted workflow is supplied for future public preflight and has not run
for this package. Stronger source routines and their stated limits remain
in the included proof modules; no historical solver campaign was repeated.
