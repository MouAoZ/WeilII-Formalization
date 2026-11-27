# Zhang’s affine-line weight bound in Lean 4

All seven results of Dingxin Zhang’s *On an Elementary Proof of Weil II* listed below passed independent acceptance. For the main theorem, a pointwise weight bound on a lisse sheaf on the affine line gives a weight bound on its first compactly supported cohomology. On the punctually pure degree-one case also proved in the Peking University development, the new proof avoids **51,700** mapped source lines of the old proof. It uses **25,476** exclusive lines in their place, for a signed saving of **26,224 lines (1.76%)**. [Paper](https://arxiv.org/pdf/2611.30749v1) · [Mathematical statements](mathematics.md) · [Proof guide](proof-guide.md)

## Theorem 1.1 and the upstream comparison

Fix a finite field $k$ of order $q$, a prime $\ell\nmid q$, an embedding $\iota:\overline{\mathbf Q}_\ell\hookrightarrow\mathbf C$, and a real $w$. Take a lisse adic sheaf $E$ on the whole arithmetic affine line. At each closed point $x$, let $q_x$ be its residue field size. Zhang assumes $|\iota(\gamma)|\le q_x^{w/2}$ for every stalk eigenvalue of geometric Frobenius. For every eigenvalue $\alpha$ on $H_c^1(\mathbf A^1_{\bar k},E)$ he proves $|\iota(\alpha)|\le q^{(w+1)/2}$. The common input for the line comparison has **equality at the stalks**. The upstream degree-one result specializes its dense-open immersion to the identity, and Zhang’s result takes the upper bound implied by purity. The two witnesses then prove the same conclusion for the same sheaf. [Exact declarations and specialization code](upstream-replacement.md) · [Lean witnesses](route-roots.json)

| Physical source lines on the common input | Old proof | New proof |
| --- | ---: | ---: |
| Upstream source used by both proofs | 1,437,842 | 1,437,842 |
| Upstream source exclusive to the old proof | 51,700 | 0 |
| Upstream source exclusive to the new proof | 0 | 7,507 |
| Project source exclusive to the new proof | 0 | 17,969 |
| **Total mapped lines** | **1,489,542** | **1,463,318** |

The denominator for both comparisons is **1,489,542**. The gross old-only share is 51,700 / 1,489,542 = **3.47%**. After charging the new-only lines, the reduction is (51,700 − 7,507 − 17,969) / 1,489,542 = **1.76%**. Adding the specialization declarations themselves, 12 old and 9 new lines, gives a saving of 26,227 / 1,489,554. Upstream also treats proper dense opens, other degrees and sheaves with singularities. No checked specialization recovers the full Zhang theorem from a pointwise upper bound alone. The number of lines removable from the upstream library as a whole is unknown. [Other callers and specializations](upstream-replacement.md)

Starting at the **seven exact target declarations**, taking their union and counting each line once gives **18,708 project lines + 1,445,641 upstream lines = 1,464,349**. The exact 1.1 declaration alone reaches 17,969 + 1,445,330 = 1,463,299 mapped lines. Connecting it to the common pure hypothesis accounts for the different new total in the table. The seven-root union reaches 295,352 declarations across all packages. In the two measured packages, 85,374 of 153,771 reached names lack precise source spans. The upstream ingredients identified for 2.2, 2.4, 2.5 and 2.6 leave parts of their conclusions unproved. A seven-target old denominator and net percentage therefore remain unknown. Separately, 28 retired purity modules account for 6,197 historical whole-file lines. Their costs enter the engineering account. [Per-target counts and coverage](upstream-replacement.md) · [Module inventory](module-inventory.tsv)

For both proofs the unit is a physical line in a half-open declaration span from the compiled position index. Internal blank lines and comments count. A span ending at column zero excludes the last line. The recount takes the union by file and line number before it computes intersections and differences. It follows actual dependencies across packages and counts source lines owned by the project or the pinned upstream library. Lean and Mathlib contribute dependencies to the traversal. Whole-file counts, missing spans and partial comparisons have separate columns. [Counting method and commands](recount.md) · [Executable counter](recount.py) · [Lean range query](route-range-query.txt)

## Frozen inputs and independent acceptance

The source revision recorded in the trace index is `1d2a35cad016e9840d47db5143d19573be9999af`. The public repository has an independent root commit. Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and Peking University’s `weil-conjectures` at `497f33d964609973fe4ed9647a1e5d32369f0d09` fix the dependencies. The full-library audit covers 389 proof inputs, including the target-import check. An independent Lake build completed 390 compilations, including the independent specification. The public package contains 388 mathematical modules and their dependency traces. A clean candidate build compiled those 388 modules in 693.236 seconds. [Dependency manifest](../lake-manifest.json) · [Frozen source and trace index](../traces/index.json)

| Results | Conclusion checked | Independent proof check |
| --- | --- | --- |
| Theorem 1.1 | Affine-line $H_c^1$ has weights at most $w+1$ | Official statement and permitted-axiom comparison, then NanoDa on the same solution export |
| Proposition 1.5 | Degree-$n$ external tensor power bound $n(w+1)+3$ | Official comparator and default Lean kernel |
| Lemma 2.1 | A uniform power-trace bound on one open complement implies the cohomology bound | Official comparator and default Lean kernel |
| Lemma 2.2 | Alternating Frobenius trace equals the signed sum over nonzero frequencies | Official comparator and default Lean kernel |
| Theorem 2.4 | A dense open of hyperplanes gives all off-middle vanishings for a quasi-finite morphism | Official comparator and default Lean kernel |
| Construction 2.5 | One smooth chain section over one finite extension gives all required vanishings | Official comparator and default Lean kernel |
| Lemma 2.6 | The finite-field chain sum obeys the stated product-of-suprema bound | Official comparator and default Lean kernel |

For each target, the receipt identifies the proof input in the full-library audit, the compiled solution, the reviewed specification, the two exports and the permitted axioms `propext`, `Classical.choice` and `Quot.sound`. The transitive declaration checks cover elaborated types and bodies, including private helpers and upstream proofs. The public index records independent acceptance for each target and a content digest for each module trace. [Semantic correspondence](mathematics.md) · [Trace index](../traces/index.json) · [Excluded weight declarations](../traces/excluded-declarations.txt)

The early line measurement and the final freeze have byte-identical public sources and Lake configuration. Some early audit artifacts were rebuilt. Against the later clean candidate used for the executable recount, the final freeze matches every module’s proof receipt and dependency trace. The two target-acceptance records refreshed after that candidate were Proposition 1.5 and Theorem 1.1. The former reused a successful default-kernel verdict on byte-identical exports. The earlier 1.1 solution export differed from the final export and its stopped replay is accounted separately. On the matched candidate the independent source-range and compiled-closure recounts both exited zero and produced byte-identical results for all 26 scopes. [Recount evidence and commands](recount.md) · [Independent acceptance](../traces/index.json)

## Resources through acceptance of all seven targets

The seventh receipt arrived on **27 November 2026 at 08:33:07.671 UTC** (16:33 Beijing time). From the first project-specific model record to that receipt, the project took **37.80184–41.44852 hours** after allowing for a quota interruption. Recorded project jobs used at least **2.51216 net CPU core-hours on WSL** and **112.75148 on ECS**, rounded to five decimals. Retiring the last ECS review service raised the ECS lower bound for the same jobs to **112.77221 core-hours**. The external model service reported **4,659,400,152 tokens**, including cached input. [Resource ledger](resources.tsv)

### Elapsed time

The earliest project-specific record is a proxy for the start, 25 November at 15:06:13 UTC. The gross duration to receipt was **149,214.671 seconds**. On 26 November, 485 quota exits affected four workers. Taking the union of their interruption intervals gives 14,774 seconds between 00:42:21 and 04:48:35 UTC. At least 1,645.953351 seconds overlapped workers that delivered results or audits that were running. Untimed work could occupy some of the remaining gaps. The supported wall-clock deduction is **0–13,128.046649 seconds**, leaving **136,086.624351–149,214.671 seconds**. Concurrent work retains its CPU and token costs. The phase intervals in the ledger are unions across both hosts and include service waits. The observed independent-review intervals total 86,856.307 seconds. They cover all 12,463.987 observed release-work seconds. [Intervals and deductions](resources.tsv)

### CPU accounting

The table gives **CPU seconds**. One core-hour is 3,600 CPU seconds. Each phase is a lower bound over identifiable jobs. Formalization includes proof development, unsuccessful routes, trial and formal compilation, and routine dependency audits. Independent review includes the specification, exports, official comparisons, kernel runs and whole-library checks. Release verification includes the public candidate build, trace checks, code measurement and reporting. Shared work includes infrastructure that served several phases. [Machine-readable phase totals](resources.tsv)

| Phase through receipt | WSL raw | WSL deduction | WSL net | ECS raw and net |
| --- | ---: | ---: | ---: | ---: |
| Formalization | 4,531.754164 | 0 | 4,531.754164 | 37,100.610000 |
| Independent review | 13,228.464958 | 9,207.800000 | 4,020.664958 | 355,401.910109 |
| Release verification and reporting | 99.732442 | 0 | 99.732442 | 12,182.450776 |
| Shared or unassigned | 391.617437 | 0 | 391.617437 | 1,220.348700 |
| **Total** | **18,251.569001** | **9,207.800000** | **9,043.769001** | **405,905.319585** |

The single WSL deduction is the cancelled Theorem 2.4 kernel. Its dependency audit, both reused exports and the ECS replay retain their costs. On WSL, 121 compiler executions added 1,184.50 seconds to the original formalization subtotal of 2,374.179529 seconds. Another 52 measured jobs used 3,712.692218 seconds. Their possible parent groups could cover at most 2,739.617583 seconds, leaving at least 973.074635 additional seconds. On ECS, 478 audits, 1,072 trial compilation jobs, two metadata jobs and one formal compilation lack native CPU readings. Failures and retries with usable counters stay in their original phases. These coverage differences limit comparisons of workload shares. [Recovery and coverage rows](resources.tsv)

The local host samples also give an estimate by activity visible at the time. The following **host CPU seconds** describe periods occupied by a single observed phase, or by mixed and unclassified activity. They contain system overhead and early I/O wait. The mixed row contains the cancelled 2.4 interval, so its host-proxy deduction represents the same 9,207.8 s already deducted from independent review in the job account. The two tables overlap.

| Activity visible in the WSL samples | Raw host proxy (CPU s) | Deduction (CPU s) | Net host proxy (CPU s) |
| --- | ---: | ---: | ---: |
| Formalization alone | 426,445.81 | 0 | 426,445.81 |
| Final review alone | 78,924.96 | 0 | 78,924.96 |
| Release work alone | 42,270.54 | 0 | 42,270.54 |
| Mixed or unassigned | 290,204.18 | 9,207.80 | 280,996.38 |
| **Observed union** | **837,845.49** | **9,207.80** | **828,637.69** |

For a direct check of the compiler figures, the main theorem’s local trial took 1.28 user + 0.85 system seconds. A distinct formal compile took 1.16 + 0.73. The two executions contribute 4.02 CPU seconds in total. Their RSS peaks were 2,596,236 and 2,600,860 KiB. An identical compiled artifact may therefore have distinct execution costs. The recovered sample comprises 66 trial compiles (643.26 CPU s) and 55 formal compiles (541.24 CPU s). [Measured job lower bounds and host context](resources.tsv)

### Independent review of Theorem 1.1

Proposition 1.5, Lemmas 2.1, 2.2 and 2.6, Theorem 2.4 and Construction 2.5 have official default-kernel receipts. For Theorem 1.1, the official comparator checked the statement and the permitted axioms. NanoDa checked the same 9,017,196,715-byte final solution export, SHA-256 `dbdbe1c50f3e12ff9b7a41cd351f7b56ef39c83addce84eae478dd71be35c597`. With 16 checker threads, NanoDa checked 297,335 declarations in **2,138.153 seconds**, with zero typechecking errors and one error printing the axiom list. Process CPU was **28,402.90 seconds**, with peak RSS of **67.76 GiB**. The enclosing service used **28,419.612288 CPU seconds** and peaked at **70 GiB**. The service contributes once to the independent-review subtotal. [Checker and service measurements](resources.tsv)

The superseded default service spent **32,916.097359 CPU seconds** on the earlier proof. The final default service had reached **10,804.358691 CPU seconds** at its last pre-receipt sample and **10,878.990583** upon retirement at 08:33:18.369 UTC. The observed increase of **74.631892 seconds** straddles receipt. Closing that invocation brings recorded independent review to **355,476.542001 ECS CPU seconds**. Earlier samples and the checker process are included in each service's lifetime counter. [Service reconciliation](resources.tsv)

On the final export, the unfinished default checker alone ran for **at least 10,140.955 seconds** and used **at least 10,138.57 CPU seconds**. Its service had spent approximately 737.761 seconds before the checker started, including 12.925 and 14.861 seconds retrieving the existing specification and solution exports. Separate timings for queueing and the statement comparison are unavailable. In a simultaneous four-second sample the default checker used 1.00 core and NanoDa used 15.96. After NanoDa finished, the 32-vCPU host used an average of 2.17 busy cores over the 6,475.746 seconds of sampled intervals through 08:32 UTC, including concurrent release work. The default checker stopped before completion, so its completed runtime and the complete-run speed ratio remain unknown. [Timing boundaries and utilization](resources.tsv)

The final export-preparation request took 546.59 s from creation to its fingerprint result, using 540.960750 service CPU s. The specification export had SHA-256 `405976729e806c4fbee663b9a0d7998c484628e19f66eaff562981f41fb34d62`. At final verification the proof audit waited 0.70 s and executed for 207.52 s. From audit completion to the default kernel’s start was 515.04 s, including retrieval of both exports, setup, comparison and any waiting. The default kernel’s observed interval until stop was 10,140.96–10,145.61 s. Its earlier, superseded counterpart had already consumed 31,138.98 process CPU s on a different solution export. Both process figures are constituents of the services above. [Checker measurements](resources.tsv)

NanoDa began about 8.61 s after its request and averaged 13.28 cores over the checker run. Near its end, differences between consecutive service CPU readings fell from 15.49 to 8.33 to 1.63 cores, followed by two roughly one-minute intervals at 1.00 core. The smaller supply of running parallel work was visible even within this multithreaded checker. NanoDa finished at 06:43:52 UTC. The final 1.1 receipt was attested at 08:32:32 and collected locally at 08:33:07. That last interval includes the decision on the acceptance method and collection of the matching official evidence. It belongs to elapsed project time. [Receipt and checker scope](../traces/index.json) · [Resource ledger](resources.tsv)

### Model usage

| Activity | All input | Cached input | Uncached input | All output | Reasoning within output |
| --- | ---: | ---: | ---: | ---: | ---: |
| Formalization | 3,682,277,004 | 3,638,835,712 | 43,441,292 | 9,093,687 | 2,959,902 |
| Independent review | 39,824,206 | 38,640,384 | 1,183,822 | 169,344 | 34,878 |
| Release verification and reporting | 186,901,630 | 184,982,528 | 1,919,102 | 458,777 | 135,162 |
| Shared or unassigned | 738,698,437 | 731,792,384 | 6,906,053 | 1,977,067 | 750,628 |
| **Total** | **4,647,701,277** | **4,594,251,008** | **53,450,269** | **11,698,875** | **3,880,570** |

Total tokens are all input plus all output. Of 790 identified sessions, 287 supplied a positive cumulative usage record. Each contributes once. The other 503 lack positive usage evidence. None of the 485 recorded failed turns returned usage. The last included token event was at 08:32:55.704 UTC. Sessions spanning several activities contribute to the shared row when their cumulative counter cannot be split. [Reported usage and coverage](resources.tsv)

### Host utilization, billing and publication

On the 16-logical-CPU local machine, the broadest sampled host estimate was **232.73486 raw and 230.17714 adjusted core-hours**. It includes operating-system activity and some early I/O wait. The conditional adjusted busy range is 227.05269–230.17714 core-hours if the early I/O-wait counter belonged to the same boot and accumulated monotonically. Sampling missed 2.41941 hours of wall time. This host estimate overlaps the job figures above. On the 32-vCPU ECS instance, matched host counters span 14.55017 hours from 26 November at 17:59:03 UTC. They measured 86.0169 busy and 379.1000 idle core-hours. Project services also ran earlier. The provider's billing dates, billable instance-hours, rate, currency, discounts and paid amount await the user's invoice. Whole-instance idle time, local electricity consumption and tariff are unknown. [Host counters and billing fields](resources.tsv)

Before receipt, a public candidate cold build completed 388 modules in **693.236 seconds**. Its service used **3,453.346817 CPU seconds**, including **3,199.17** for its compilers. The successful-compile and attempt logs describe the same 388 executions. Reuse of this build carries its original charge. Two separate public trace checks used 17.581217 and 4.722742 CPU seconds. [Release verification](resources.tsv)

The publication checkpoint is **08:42 UTC**, separate from the receipt cutoff. Private evidence collection recorded WSL at 08:35:32 and ECS at 08:35:35. WSL verified an **866,358,205-byte** preview bundle at 08:40:48. Its CPU was unmetered. Five measured reporting jobs that both started and finished after receipt used **19.91 ECS CPU seconds**. A further report computation ran from 07:46:08 to 08:40:36 and used **3,280.67 CPU seconds**. Its CPU split at receipt is unknown, so the ledger records its lifetime separately. Final public-package verification, final private archiving and subsequent reporting have open costs at the publication checkpoint. [Post-receipt rows](resources.tsv)

Through local collection, timed formalization work occupied 84,477.915 s, final independent review 86,856.307 s, release verification and reporting 12,463.987 s, and shared work 6,286.454 s. The union across all four was 133,592.076 s. An interval counts once within each phase. The calendar duration also includes gaps for which no running work was observed. Only the supported quota-stall deduction applies to the project’s elapsed time. [Activity unions](resources.tsv)

For a single cloud instance at a constant price $r$ per instance-hour, a conditional compute-only charge is $r$ times its billable running hours. The 14.55017-hour observed same-boot span corresponds to $14.55017r$ for that span **if** it was billed continuously at that rate. It excludes earlier work and any disk, transfer, discounts or taxes. Simultaneous proof and review share that charge. No reliable price per hour saved or project-wide cloud speedup follows from the available evidence. [Billing and idle coverage](resources.tsv)

Of the observed phase intervals, at least 37,742.146 s (10.48 h) were common to formalization and final independent review. This intersection uses service intervals, completed worker runs and timed jobs with matching endpoints, and merges overlaps on each host before taking their combined intersection. Reassigning all idle cloud core-hours to either phase would mix instance billing with CPU consumption. [Phase coverage](resources.tsv)

## What parallel hardware bought

### Paired runs on the same proof input

These are full transitive dependency audits. In each pair, the compiled input and the uncompressed declaration trace agree. Admission starts when an audit requests memory. Execution starts on admission and ends when the audit completes. Publication can wait for other modules in the same delivery. The two runs of 2.4 on WSL face different concurrent loads and share a single ECS comparison run. [Paired measurements](resources.tsv)

| Target | WSL queue / execution (s) | ECS queue / execution (s) | Execution ratio, WSL / ECS | Request through audit finish, WSL / ECS |
| --- | ---: | ---: | ---: | ---: |
| Theorem 2.4, first WSL run | 327.1 / 149.3 | 0.0009 / 152.3 | 0.98× | 3.13× |
| Theorem 2.4, second WSL run | 1,227.3 / 269.6 | Same run | 1.77× | 9.83× |
| Construction 2.5 | 7,262 / 273 | 0.001 / 151.42 | 1.80× | 49.76× |

In the first 2.4 pair the local execution finished three seconds sooner. On 2.5 remote admission saved about two hours of queueing. One transfer of the two 2.4 official exports and configuration (8,801,379,034 bytes) sent 1,088,438,977 bytes after compression. Comparable transfer and final integration timestamps for each member of the pairs are unavailable. One later cloud-assisted 2.5 repair took 165 s from assignment to delivery and 321 s from delivery to publication. Its subsequent independent check had to wait for the separate specification. That interval has a different input and endpoint from the paired audit. [Module proofs](../traces/index.json) · [Timing account](resources.tsv)

### Where local deliveries waited

The local guest had 16 logical CPUs and 24,170,140 KiB of RAM (23.05 GiB). A heavy independent 2.4 kernel reserved 16 GiB out of the 19,975,836 KiB available for reservations after the 4 GiB host allowance. Only 3,198,620 KiB were left. All 37 modules in 19 waiting deliveries lacked an audit that fitted that budget under the measured peaks and margins. The smallest previously measured full audit needed 2,658,272 KiB plus a 25% margin. Once the kernel released its reservation, the 2.5 repair reached publication at 08:25 UTC, with a measured peak of 12.21 GiB. The CPU deduction for the interrupted kernel preserves this historical wait in the time series. [Resource ledger](resources.tsv)

| 26 Nov 2026, UTC | Lean deliveries accepted | Delivery to publication, median / P95 (s) | Still pending / oldest age (s) | Median available RAM (GiB) | Median CPU idle | Peak sampled paging (MiB/s) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 07:00–08:00 | 0 | — | 25 / 11,354 | 8.37 | 51.3% | 10.00 |
| 08:00–09:00 | 9 | 13,175 / 13,628 | 19 / 13,026 | 16.98 | 51.4% | 76.16 |
| 12:00–13:00 | 20 | 250 / 1,606.6 | 6 / 1,003 | 18.03 | 58.9% | 10.19 |

The rows pair WSL acceptance events with 239, 238 and 237 scheduler observations, respectively. Minimum available RAM was 1.68, 4.21 and 10.76 GiB. Paging is observed swap traffic during a sampling interval. Across 226 historical matched Lean deliveries the median delivery-to-publication time was 1,380 s and P95 was 12,345 s. Batches, priority changes, proof dependencies and retries affect these times. During an earlier quota interruption some existing proofs and audits still ran. Neither hourly throughput nor an individual queue saving determines how much earlier the seventh receipt could have landed. [Throughput and elapsed-time accounting](resources.tsv)

### Sizing compilation and routine proof audits

For formalization alone, a light Künneth tensor-square proof compiled and passed its interface check in an 821 MiB process group. Another formal compile used 1,741,696 KiB RSS and its corresponding routine full audit used 4,913,392 KiB. An earlier routine geometry audit reached 15,353,140 KiB. On the home guest, one large geometric audit could run, and a contemporaneous compiler or a second audit could consume the remaining headroom. Compilation and per-proof audits have distinct working sets. Model inference used an external service. [Compilation and audit measurements](resources.tsv)

Using **12–16 GiB per heavy routine audit**, a 25% reservation margin and 4–8 GiB for the guest and light workers gives planning envelopes of **19–28 GiB for one** or **34–48 GiB for two**. These are arithmetic scenarios using formalization workloads, with no credit for shared memory pages and no concurrent independent kernel. An unmeasured input or a concurrent large compilation can exceed the envelope. Conversely, measured shared file-backed pages reduce the combined commitment. The scheduler gave credit only for observed sharing and separately reserved room for future growth. Extra workers can prepare independent proofs but do little for the rate of publication when every ready proof is waiting for memory. [Resource ledger](resources.tsv)

Historical timing distributions through 05:10 UTC on 27 November are shown below. They include the jobs for which both execution endpoints survived, across the activities present in each workload. They describe the job mix and complement the smaller formalization-only CPU samples. A multi-module trial can contribute several module timings.

| Timed workload | Runs | Median queue (s) | Execution, median / P95 (s) | Peak RSS, median / P95 (KiB) |
| --- | ---: | ---: | ---: | ---: |
| WSL dependency audits | 367 | 48.01 | 76.18 / 256.65 | 11,573,276 / 15,528,559 |
| ECS native dependency audits | 522 | 168.69 | 29.07 / 138.40 | 12,422,572 / 17,309,103 |
| ECS formal compiles | 9 | 0.81 | 3.80 / 9.34 | 3,388,276 / 12,069,750 |
| ECS trial compiles | 660 | 16.65 | 18.30 / 120.35 | 4,079,270 / 11,660,574 |

A separate ECS sample through final receipt retains in-sandbox native user and system CPU and an unambiguous formalization job class. It includes 39 trial-profile jobs (435.17 CPU s), eight formal compiles (46.55 CPU s), six ordinary audits (1,547.28 CPU s) and one joint audit (430.01 CPU s). Each execution contributes once after matching copies by job identity. These are observed subsets of the project jobs, with CPU totals of 0.121, 0.013, 0.430 and 0.119 core-hours respectively. Cache hits, missing historical counters, enclosing group measurements and the mix of inputs prevent extrapolation from these samples to a full cost per compile. [Job distributions and coverage](resources.tsv)

### Running the same independent checks

The cloud host had 32 vCPUs and nominally 128 GiB of RAM. Five independent default kernels each used about one core. Over 14 one-minute samples their host was 16.1% busy at the median. When other cores took independent audits, a later 17-sample window reached 46.3% median utilization and completed 22 module audits. That is overlap between ready jobs. On a single fixed proof closure a different traversal algorithm cut 146.6 s to 55.0 s at roughly 14.2 GiB RSS. In a separate thread-count test, four threads took 9.36 s and eight took 9.57 s. Caching and the change of traversal affect comparisons across runs. [Job evidence](resources.tsv)

For **the actual seven-target acceptance policy**, even a serial schedule must accommodate the 16-thread 1.1 NanoDa run. It peaked at 67.76 GiB process RSS and 70 GiB for its group with zero swap. The scheduler ultimately budgeted 93.75 GiB for that group. At the 12 GiB host allowance this is about 106 GiB before other heavy jobs. A dedicated 96 GiB host has capacity above the observed isolated peak but less than the observed reservation plus host allowance. The 128 GiB host demonstrated this configuration and also accommodated the single-core replay. The shared data disk was 500 GiB, with roughly 60 GiB already used by the toolchain, packages and initial export at deployment. Keeping additional exports, compiled views, traces and temporary files increases that footprint. These observations support serial local proof development, selective cloud audits during a backlog, and a larger memory window for final 1.1 acceptance. A completed end-to-end home-only run, equivalent measurements at intermediate sizes and local electricity charges are unavailable. [Checker and billing coverage](resources.tsv)

The six successful default-comparator invocations took 45.050 s (2.6), 41,480.000 s (2.4), 42,963.567 s (2.5), 50,166.106 s (2.2), 50,877.916 s (2.1) and 56,156.987 s (1.5). Their reported comparator peaks ranged from 510,588 to 17,009,348 KiB. Each of the six represents a distinct successful invocation on accepted bytes, including historical invocations whose exports matched. Adding their measured durations and the 2,138.153 s NanoDa checker gives **67.73 hours** if these seven operations run one after another at the observed speeds. With all inputs immediately ready, unlimited memory and the same per-job speeds, the longest such operation gives an ideal lower bound of **15.60 hours**. These calculations cover the specified comparison and kernel operations. Producing exports, the separate 1.1 statement comparison, admissions, proof dependencies and collection add time. Neither scenario is a measurement of the whole project. [Checker policy and export identities](../traces/index.json) · [Observed project elapsed time](resources.tsv)

## Reproducing the public results

Run the following from the root of the public checkout. The two revisions printed first identify the public root and the frozen mathematical source. The upstream checkout must match the separate upstream hash. The quick recount verifies the counted source files, scopes and frozen line ranges. The full recount rebuilds the dependency closures and source spans using the pinned Lean packages. The appendix gives both commands, including the upstream modules to build and a sequential option for constrained machines. [Recount instructions](recount.md) · [Counter](recount.py) · [Roots and witnesses](route-roots.json) · [Lean source-range query](route-range-query.txt)

```sh
git rev-list --max-parents=0 HEAD
python3 -c 'import json; print(json.load(open("traces/index.json"))["sourceRevision"])'
lake build
upstream=.lake/packages/weil-conjectures
test "$(git -C "$upstream" rev-parse HEAD)" = 497f33d964609973fe4ed9647a1e5d32369f0d09
run_dir=$(mktemp -d)
python3 docs/recount.py --root . --upstream "$upstream" --output "$run_dir/ranges.json"
```

Use the public inventory for arithmetic without loading Lean. In this example the denominator for the pure case includes its shared lines. The one-sided seven-target entry has no corresponding full upstream derivation.

```sh
python3 - <<'PY'
import csv
from collections import Counter

fields = ("old_only_lines", "new_project_only_lines", "new_upstream_only_lines", "shared_lines")
totals = {key: Counter() for key in ("pure-degree-one", "seven-native")}
with open("docs/module-inventory.tsv", newline="", encoding="utf-8") as table:
    for row in csv.DictReader(table, delimiter="\t"):
        for key in totals.keys() & set(row["scopes"].split(",")):
            totals[key].update({field: int(row[field]) for field in fields})
o, p, u, c = (totals["pure-degree-one"][field] for field in fields)
print("Pure case: gross avoided, net saved, old denominator:", o, o-p-u, o+c)
print("Seven targets: project and upstream lines:",
      *(totals["seven-native"][field] for field in fields[1:3]))
PY
```

The public data support arithmetic checks on the published resource subtotals, phase deductions and bounds. Session-level counters, private execution records and host attribution require their original monitoring data. Unknown billing and sampling fields remain missing. [Resource ledger](resources.tsv) · [Following a proof trace](proof-guide.md#reading-a-proof-trace)

To reproduce the net CPU figures at collection time, sum the four additive phase rows for each host. Divide CPU seconds by 3,600. Elapsed-time bounds already include the quota adjustment. The combined model figure includes all input and all output.

```sh
python3 - <<'PY'
import csv
from collections import defaultdict
from decimal import Decimal

with open("docs/resources.tsv", newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream, delimiter="\t"))
hours = defaultdict(Decimal)
for row in rows:
    if row["metric"] == "project_cpu":
        hours[row["host"]] += Decimal(row["net"]) / 3600
    if row["metric"] in ("elapsed_lower_bound", "elapsed_upper_bound"):
        print(row["metric"], Decimal(row["net"]) / 3600, "hours")
for host, value in sorted(hours.items()):
    print(host, f"{value:.5f}", "net core-hours")
model = [r for r in rows if r["host"] == "Model service" and r["activity"] == "All recorded phases"]
print("Reported tokens:", sum(int(r["value"]) for r in model if r["metric"] in ("input_tokens", "output_tokens")))
PY
```
