(** * StoreSafety.v — Stable interface for Mooncake KV cache store safety

    Tier: interface    Admits: 0    Axioms: 0

    Downstream consumers import this module, not mooncake_formal internals.
    Re-exports mooncake_formal's headline theorems with stable names and
    self-contained types.

    Exported guarantees:

    - [reads_protected]: read-in-progress objects cannot be evicted,
      even under arbitrary concurrent activity on other objects.
    - [reads_constructive]: any COMPLETE object is readable
      (a BeginRead step exists).
    - [reads_transparent]: balanced read sessions (BeginRead then
      EndRead) leave store state unchanged.
    - [drain_safe]: segment drain preserves actively-read objects.
    - [batch_eviction]: batch eviction of non-targeted objects
      preserves actively-read objects.
    - [global_invariant]: store_well_formed (consistent + coherent +
      NoDup) is preserved by every step under place_fresh.
    - [consistency_invariant]: store_consistent alone is preserved
      by every step unconditionally.
    - [refcount_balance]: refcount equals the difference between
      BeginRead and EndRead counts in the trace.
    - [protection_dichotomy_thm]: every object is either protected
      (eviction impossible) or evictable (eviction possible).

    @source Mooncake
    @fidelity specification
    @abstraction interface

    Template: comms_formal/theories/Interface/CollectiveTermination.v *)

Require Export MooncakeFormal.Core.Core.
Require Export MooncakeFormal.Composition.StoreComposition.
Require Export MooncakeFormal.Store.RefcountProtocol.
Require Export MooncakeFormal.LTS.EvictionSafety.
Require Export MooncakeFormal.LTS.TraceEquivalence.
Require Export MooncakeFormal.LTS.RefcountCounting.
Require Export MooncakeFormal.LTS.ProtectionFrame.
Require Export MooncakeFormal.LTS.CapacityCoherence.
Require Export MooncakeFormal.LTS.NoDupPreservation.
Require Export MooncakeFormal.LTS.GlobalSafety.

(** Serving Safety *)

Definition reads_protected := serving_safety.
Definition reads_constructive := serving_path.

(** Read Transparency *)

Definition reads_transparent := reads_are_transparent.

(** Drain Safety *)

Definition drain_safe := drain_respects_readers.
Definition batch_eviction := batch_eviction_safe.

(** Global Invariant *)

Definition global_invariant := invariant_preservation.
Definition consistency_invariant := consistency_always_preserved.

(** Refcount Accounting *)

Definition refcount_balance := refcount_is_read_balance.
Definition protection_dichotomy_thm := protection_dichotomy.
