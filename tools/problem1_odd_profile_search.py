#!/usr/bin/env python3

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
from math import comb
from typing import Dict, Iterable, List, Sequence, Set, Tuple


GREEN_BOLD = "\033[1;32m"
RED_BOLD = "\033[1;31m"
RESET = "\033[0m"


Family = Tuple[int, ...]


@dataclass(frozen=True)
class PairInterfaceCounterexample:
    n: int
    e: int
    target: int
    lhs: int
    family_n: Family
    family_m: Family


@dataclass(frozen=True)
class MinimalOutsideCounterexample:
    n: int
    middle: int
    minimum: int
    family: Family
    minimal_outside: Family


@dataclass(frozen=True)
class BoundaryAntichainFailure:
    n: int
    boundary_size: int
    middle: int
    family: Family
    boundary: Family


@dataclass(frozen=True)
class UpperTailPrismGapCounterexample:
    n: int
    e: int
    target: int
    boundary_size: int
    witness_total_size: int
    prism_total_size: int
    outside_rank: int
    family_n: Family
    family_m: Family


@dataclass(frozen=True)
class StructuredUpperTailPrismGapResult:
    name: str
    n: int
    e: int
    target: int
    exact_upper_downset_search: bool
    best_upper_downset_size: int
    upper_total_size_gain_over_simple_lower_budget: int
    upper_boundary_size: int
    outside_support_ranks: Tuple[int, ...]
    best_destroyed_outside_rank4: int
    min_prism_boundary: int


@dataclass(frozen=True)
class StructuredFirstGapDefectResult:
    name: str
    n: int
    e: int
    target: int
    upper_profile: Tuple[int, ...]
    weighted_upper_tail_gain: int
    exact_upper_downset_search: bool
    best_upper_downset_size: int
    upper_boundary_size: int
    best_destroyed_outside_rank4: int
    min_prism_boundary: int


@dataclass(frozen=True)
class StructuredUniformUpperMiddleLayerResult:
    name: str
    n: int
    e: int
    upper_shadow_size: int
    max_t_v_outside: int
    reduced_margin: int
    best_v: Family
    best_t_v_outside: Family


@dataclass(frozen=True)
class ColexUniformUpperMiddleLayerResult:
    n: int
    e: int
    upper_shadow_size: int
    t_v_size: int
    t_v_outside_size: int
    reduced_margin: int


@dataclass(frozen=True)
class ColexUniformUpperMiddleLayerSummary:
    n: int
    all_reduced_margins_nonnegative: bool
    all_t_v_outside_zero: bool
    worst_reduced_margin: int
    worst_reduced_margin_e: int
    max_t_v_outside_size: int
    max_t_v_outside_e: int
    sample_count: int


@dataclass(frozen=True)
class ExhaustiveColexDefectReductionFailure:
    n: int
    e: int
    colex_delta: int
    witness_delta: int
    colex_u_family: Family
    colex_v_family: Family
    witness_u_family: Family
    witness_v_family: Family


@dataclass(frozen=True)
class MiddleLayerCompressionCounterexample:
    n: int
    i: int
    j: int
    u_family: Family
    v_family: Family
    t_v_outside: Family
    compressed_u_family: Family
    compressed_v_family: Family
    compressed_t_v_outside: Family
    compressed_image_of_t_v_outside: Family
    delta_before: int
    delta_after: int


def all_subsets(n: int) -> Tuple[int, ...]:
    subsets: List[int] = []
    for r in range(n + 1):
        for items in combinations(range(n), r):
            mask = 0
            for item in items:
                mask |= 1 << item
            subsets.append(mask)
    return tuple(subsets)


def subset_cardinality(mask: int) -> int:
    return mask.bit_count()


def enumerate_antichains(subsets: Sequence[int]) -> List[Tuple[int, ...]]:
    order = sorted(subsets, key=lambda mask: (subset_cardinality(mask), mask), reverse=True)
    comparable: Dict[int, Set[int]] = {mask: set() for mask in subsets}
    for left in subsets:
        for right in subsets:
            if (left & right) == left or (left & right) == right:
                comparable[left].add(right)

    antichains: List[Tuple[int, ...]] = []
    chosen: List[int] = []

    def go(index: int, forbidden: Set[int]) -> None:
        if index == len(order):
            antichains.append(tuple(chosen))
            return
        current = order[index]
        go(index + 1, forbidden)
        if current not in forbidden:
            chosen.append(current)
            go(index + 1, forbidden | comparable[current])
            chosen.pop()

    go(0, set())
    return antichains


def antichain_to_downset(antichain: Iterable[int], subsets: Sequence[int]) -> Family:
    antichain_tuple = tuple(antichain)
    family = [
        subset for subset in subsets
        if any((subset & maximal) == subset for maximal in antichain_tuple)
    ]
    return tuple(sorted(family))


def enumerate_downsets(n: int) -> Tuple[Tuple[int, ...], List[Family]]:
    subsets = all_subsets(n)
    antichains = enumerate_antichains(subsets)
    downsets = [antichain_to_downset(antichain, subsets) for antichain in antichains]
    return subsets, downsets


def positive_boundary(family: Family, subsets: Sequence[int]) -> Set[int]:
    family_set = set(family)
    boundary: Set[int] = set()
    for subset in subsets:
        if subset in family_set:
            continue
        candidates = subset
        while candidates:
            bit = candidates & -candidates
            if (subset ^ bit) in family_set:
                boundary.add(subset)
                break
            candidates ^= bit
    return boundary


def minimal_outside(family: Family, subsets: Sequence[int]) -> Set[int]:
    family_set = set(family)
    outside: Set[int] = set()
    for subset in subsets:
        if subset in family_set:
            continue
        candidates = subset
        is_minimal = True
        while candidates:
            bit = candidates & -candidates
            if (subset ^ bit) not in family_set:
                is_minimal = False
                break
            candidates ^= bit
        if is_minimal:
            outside.add(subset)
    return outside


def format_subset(mask: int) -> str:
    if mask == 0:
        return "{}"
    elements = [str(index) for index in range(mask.bit_length()) if mask & (1 << index)]
    return "{" + ", ".join(elements) + "}"


def format_family(family: Family) -> str:
    return "[" + ", ".join(format_subset(mask) for mask in family) + "]"


def is_antichain(family: Iterable[int]) -> bool:
    members = tuple(family)
    for index, left in enumerate(members):
        for right in members[index + 1 :]:
            if (left & right) == left or (left & right) == right:
                return False
    return True


def render_progress(done: int, total: int, label: str, width: int = 28) -> None:
    filled = width * done // total
    bar = "#" * filled + "-" * (width - filled)
    print(f"\r[{bar}] {done}/{total} {label}", end="", flush=True)
    if done == total:
        print()


def ok(message: str) -> None:
    print(f"{GREEN_BOLD}{message}{RESET}")


def warn(message: str) -> None:
    print(f"{RED_BOLD}{message}{RESET}")


def profile_table(
    n: int,
    downsets: Sequence[Family],
    boundary_cache: Dict[Family, Set[int]],
    max_excess: int,
) -> List[Tuple[int, int, int]]:
    half = 2 ** (n - 1)
    table: List[Tuple[int, int, int]] = []
    for size in range(half, min(2 ** n, half + max_excess) + 1):
        min_boundary = min(len(boundary_cache[family]) for family in downsets if len(family) == size)
        table.append((size, size - half, min_boundary))
    return table


def total_size(family: Family) -> int:
    return sum(subset_cardinality(subset) for subset in family)


def initial_segment_mask(size: int) -> int:
    return (1 << size) - 1


def representative_pair_generators(
    n: int, left_rank: int, right_rank: int, intersection: int
) -> Tuple[int, int]:
    min_intersection = max(0, left_rank + right_rank - n)
    if intersection < min_intersection or intersection > min(left_rank, right_rank):
        raise ValueError("invalid intersection size for representative pair")
    left = initial_segment_mask(left_rank)
    right = initial_segment_mask(intersection)
    next_index = left_rank
    for offset in range(right_rank - intersection):
        right |= 1 << (next_index + offset)
    return (left, right)


def slice_cardinality(family: Iterable[int], rank: int) -> int:
    return sum(1 for subset in family if subset_cardinality(subset) == rank)


def rank_subsets(n: int, rank: int, subsets: Sequence[int]) -> Tuple[int, ...]:
    del n
    return tuple(sorted(subset for subset in subsets if subset_cardinality(subset) == rank))


def colex_key(mask: int) -> Tuple[int, ...]:
    elements = [index for index in range(mask.bit_length()) if mask & (1 << index)]
    return tuple(reversed(elements))


def colex_initial_segment(n: int, rank: int, size: int, subsets: Sequence[int]) -> Family:
    rank_family = rank_subsets(n, rank, subsets)
    ordered = sorted(rank_family, key=colex_key)
    return tuple(ordered[:size])


def compress_mask(mask: int, i: int, j: int) -> int:
    if i == j:
        return mask
    i_bit = 1 << i
    j_bit = 1 << j
    if mask & j_bit and not (mask & i_bit):
        return (mask ^ j_bit) | i_bit
    return mask


def compress_uniform_family(family: Sequence[int], i: int, j: int) -> Family:
    family_set = set(family)
    compressed = set(family_set)
    for member in family:
        image = compress_mask(member, i, j)
        if image != member and image not in family_set:
            compressed.remove(member)
            compressed.add(image)
    return tuple(sorted(compressed))


def even_lower_half_total_size_in_prism_dimension(n: int) -> int:
    m = n // 2
    return (n + 1) * (2 ** (n - 1)) - (m + 1) * comb(n, m)


def lower_half_family(n: int, subsets: Sequence[int]) -> Family:
    midpoint = n // 2
    return tuple(sorted(subset for subset in subsets if subset_cardinality(subset) <= midpoint))


def downset_from_generators_above_lower_half(
    n: int, subsets: Sequence[int], generators: Sequence[int]
) -> Family:
    midpoint = n // 2
    generator_tuple = tuple(generators)
    return tuple(
        sorted(
            subset
            for subset in subsets
            if subset_cardinality(subset) <= midpoint
            or any((subset & generator) == subset for generator in generator_tuple)
        )
    )


def max_destroyed_rank4_targets_by_available_rank3_sets(
    target_rank4_sets: Sequence[int], available_rank3_sets: Sequence[int], budget: int
) -> int:
    triple_index = {subset: index for index, subset in enumerate(available_rank3_sets)}
    target_masks: List[int] = []
    for rank4_set in target_rank4_sets:
        triple_mask = 0
        valid_target = True
        candidates = rank4_set
        while candidates:
            bit = candidates & -candidates
            triple = rank4_set ^ bit
            triple_position = triple_index.get(triple)
            if triple_position is None:
                valid_target = False
                break
            triple_mask |= 1 << triple_position
            candidates ^= bit
        if valid_target:
            target_masks.append(triple_mask)
    dp: Dict[int, int] = {0: 0}
    for target_mask in target_masks:
        updates: Dict[int, int] = {}
        for union_mask, destroyed in dp.items():
            new_union_mask = union_mask | target_mask
            if new_union_mask.bit_count() > budget:
                continue
            current = updates.get(new_union_mask)
            if current is None or current < destroyed + 1:
                updates[new_union_mask] = destroyed + 1
        for union_mask, destroyed in updates.items():
            current = dp.get(union_mask)
            if current is None or current < destroyed:
                dp[union_mask] = destroyed
    return max(dp.values())


def max_destroyed_rank4_targets_by_rank3_budget(
    n: int, subsets: Sequence[int], target_rank4_sets: Sequence[int], budget: int
) -> int:
    del n
    available_rank3_sets = [subset for subset in subsets if subset_cardinality(subset) == 3]
    return max_destroyed_rank4_targets_by_available_rank3_sets(
        target_rank4_sets, available_rank3_sets, budget
    )


def upper_downsets(upper_part: Sequence[int]) -> List[Tuple[int, ...]]:
    upper_tuple = tuple(upper_part)
    lower_upper_elements = {
        upper_element: tuple(
            candidate
            for candidate in upper_tuple
            if candidate != upper_element and (candidate & upper_element) == candidate
        )
        for upper_element in upper_tuple
    }
    downsets: List[Tuple[int, ...]] = []
    for chosen_mask in range(1 << len(upper_tuple)):
        chosen = {
            upper_tuple[index]
            for index in range(len(upper_tuple))
            if chosen_mask & (1 << index)
        }
        if all(all(candidate in chosen for candidate in lower_upper_elements[upper_element]) for upper_element in chosen):
            downsets.append(tuple(sorted(chosen)))
    return downsets


def support_rank3_sets_of_upper_downset(upper_downset: Sequence[int]) -> Set[int]:
    support: Set[int] = set()
    for upper_element in upper_downset:
        candidates = upper_element
        while candidates:
            bit = candidates & -candidates
            rank3_subset = upper_element ^ bit
            if subset_cardinality(rank3_subset) == 3:
                support.add(rank3_subset)
            candidates ^= bit
    return support


def outside_high_boundary_count_from_upper_downset(
    upper_downset: Sequence[int], family_n_set: Set[int], subsets: Sequence[int]
) -> int:
    upper_downset_set = set(upper_downset)
    count = 0
    for subset in subsets:
        if subset in family_n_set or subset_cardinality(subset) <= 4:
            continue
        candidates = subset
        while candidates:
            bit = candidates & -candidates
            predecessor = subset ^ bit
            if predecessor in upper_downset_set:
                count += 1
                break
            candidates ^= bit
    return count


def upper_shadow_of_uniform_middle_family(
    upper_family: Sequence[int], subsets: Sequence[int]
) -> Tuple[int, ...]:
    if not upper_family:
        return ()
    upper_family_set = set(upper_family)
    ambient_rank = subset_cardinality(upper_family[0])
    target_rank = ambient_rank + 1
    shadow = [
        subset
        for subset in subsets
        if subset_cardinality(subset) == target_rank
        and any((member & subset) == member for member in upper_family_set)
    ]
    return tuple(sorted(shadow))


def t_of_v_rank4_family(v_family: Sequence[int], subsets: Sequence[int]) -> Tuple[int, ...]:
    v_set = set(v_family)
    targets = []
    for subset in subsets:
        if subset_cardinality(subset) != 4:
            continue
        candidates = subset
        all_triples_present = True
        while candidates:
            bit = candidates & -candidates
            triple = subset ^ bit
            if triple not in v_set:
                all_triples_present = False
                break
            candidates ^= bit
        if all_triples_present:
            targets.append(subset)
    return tuple(sorted(targets))


def t_of_v_family(v_family: Sequence[int], subsets: Sequence[int]) -> Family:
    if not v_family:
        return ()
    source_rank = subset_cardinality(v_family[0])
    target_rank = source_rank + 1
    v_set = set(v_family)
    targets: List[int] = []
    for subset in subsets:
        if subset_cardinality(subset) != target_rank:
            continue
        candidates = subset
        all_predecessors_present = True
        while candidates:
            bit = candidates & -candidates
            predecessor = subset ^ bit
            if predecessor not in v_set:
                all_predecessors_present = False
                break
            candidates ^= bit
        if all_predecessors_present:
            targets.append(subset)
    return tuple(sorted(targets))


def middle_layer_badness(u_family: Sequence[int], v_family: Sequence[int], subsets: Sequence[int]) -> int:
    t_v = t_of_v_family(v_family, subsets)
    t_v_outside = tuple(subset for subset in t_v if subset not in set(u_family))
    upper_shadow = upper_shadow_of_uniform_middle_family(u_family, subsets)
    return len(t_v_outside) - len(upper_shadow)


def exhaustive_colex_defect_reduction_failure(
    n: int,
) -> ExhaustiveColexDefectReductionFailure | None:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank = middle
    upper_rank = middle + 1
    lower_rank_sets = rank_subsets(n, lower_rank, subsets)
    upper_rank_sets = rank_subsets(n, upper_rank, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    upper_shadow_sizes: Dict[int, int] = {}
    t_v_masks: Dict[int, int] = {}

    for u_mask in range(1 << upper_count):
        u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        upper_shadow_sizes[u_mask] = len(upper_shadow_of_uniform_middle_family(u_family, subsets))

    upper_index = {subset: index for index, subset in enumerate(upper_rank_sets)}
    for v_mask in range(1 << lower_count):
        v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        t_v_family = t_of_v_family(v_family, subsets)
        t_mask = 0
        for subset in t_v_family:
            t_mask |= 1 << upper_index[subset]
        t_v_masks[v_mask] = t_mask

    colex_u_masks: Dict[int, int] = {}
    colex_v_masks: Dict[int, int] = {}
    for e in range(lower_count + 1):
        colex_u_family = colex_initial_segment(n, upper_rank, e, subsets)
        colex_v_family = colex_initial_segment(n, lower_rank, e, subsets)
        u_mask = 0
        for subset in colex_u_family:
            u_mask |= 1 << upper_index[subset]
        v_mask = 0
        lower_index = {subset: index for index, subset in enumerate(lower_rank_sets)}
        for subset in colex_v_family:
            v_mask |= 1 << lower_index[subset]
        colex_u_masks[e] = u_mask
        colex_v_masks[e] = v_mask

    for e in range(lower_count + 1):
        colex_u_mask = colex_u_masks[e]
        colex_v_mask = colex_v_masks[e]
        colex_t_outside = (t_v_masks[colex_v_mask] & ~colex_u_mask).bit_count()
        colex_delta = colex_t_outside - upper_shadow_sizes[colex_u_mask]
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            upper_shadow_size = upper_shadow_sizes[u_mask]
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                witness_delta = (t_v_masks[v_mask] & ~u_mask).bit_count() - upper_shadow_size
                if witness_delta > colex_delta:
                    colex_u_family = tuple(
                        upper_rank_sets[index]
                        for index in range(upper_count)
                        if colex_u_mask & (1 << index)
                    )
                    colex_v_family = tuple(
                        lower_rank_sets[index]
                        for index in range(lower_count)
                        if colex_v_mask & (1 << index)
                    )
                    witness_u_family = tuple(
                        upper_rank_sets[index]
                        for index in range(upper_count)
                        if u_mask & (1 << index)
                    )
                    witness_v_family = tuple(
                        lower_rank_sets[index]
                        for index in range(lower_count)
                        if v_mask & (1 << index)
                    )
                    return ExhaustiveColexDefectReductionFailure(
                        n=n,
                        e=e,
                        colex_delta=colex_delta,
                        witness_delta=witness_delta,
                        colex_u_family=colex_u_family,
                        colex_v_family=colex_v_family,
                        witness_u_family=witness_u_family,
                        witness_v_family=witness_v_family,
                    )
    return None


def canonical_middle_layer_compression_inclusion_counterexample_n7() -> MiddleLayerCompressionCounterexample:
    n = 7
    subsets = all_subsets(n)
    all_rank4_sets = rank_subsets(n, 4, subsets)
    i, j = 0, 2
    b = sum(1 << index for index in (2, 3, 4, 5))
    v_family = tuple(sorted(b ^ (1 << index) for index in (2, 3, 4, 5)))
    b_compressed = compress_mask(b, i, j)
    filler = tuple(subset for subset in all_rank4_sets if subset not in {b, b_compressed})
    u_family = tuple(sorted((b_compressed,) + filler[:3]))
    t_v_outside = tuple(subset for subset in t_of_v_family(v_family, subsets) if subset not in set(u_family))
    compressed_u_family = compress_uniform_family(u_family, i, j)
    compressed_v_family = compress_uniform_family(v_family, i, j)
    compressed_t_v_outside = tuple(
        subset
        for subset in t_of_v_family(compressed_v_family, subsets)
        if subset not in set(compressed_u_family)
    )
    compressed_image_of_t_v_outside = compress_uniform_family(t_v_outside, i, j)
    return MiddleLayerCompressionCounterexample(
        n=n,
        i=i,
        j=j,
        u_family=u_family,
        v_family=v_family,
        t_v_outside=t_v_outside,
        compressed_u_family=compressed_u_family,
        compressed_v_family=compressed_v_family,
        compressed_t_v_outside=compressed_t_v_outside,
        compressed_image_of_t_v_outside=compressed_image_of_t_v_outside,
        delta_before=middle_layer_badness(u_family, v_family, subsets),
        delta_after=middle_layer_badness(compressed_u_family, compressed_v_family, subsets),
    )


def search_canonical_middle_layer_delta_failure_n7() -> MiddleLayerCompressionCounterexample | None:
    n = 7
    subsets = all_subsets(n)
    all_rank4_sets = rank_subsets(n, 4, subsets)
    i, j = 0, 2
    b = sum(1 << index for index in (2, 3, 4, 5))
    v_family = tuple(sorted(b ^ (1 << index) for index in (2, 3, 4, 5)))
    for u_family in combinations(all_rank4_sets, len(v_family)):
        compressed_u_family = compress_uniform_family(u_family, i, j)
        compressed_v_family = compress_uniform_family(v_family, i, j)
        delta_before = middle_layer_badness(u_family, v_family, subsets)
        delta_after = middle_layer_badness(compressed_u_family, compressed_v_family, subsets)
        if delta_before > delta_after:
            t_v_outside = tuple(
                subset for subset in t_of_v_family(v_family, subsets) if subset not in set(u_family)
            )
            compressed_t_v_outside = tuple(
                subset
                for subset in t_of_v_family(compressed_v_family, subsets)
                if subset not in set(compressed_u_family)
            )
            compressed_image_of_t_v_outside = compress_uniform_family(t_v_outside, i, j)
            return MiddleLayerCompressionCounterexample(
                n=n,
                i=i,
                j=j,
                u_family=tuple(sorted(u_family)),
                v_family=v_family,
                t_v_outside=t_v_outside,
                compressed_u_family=compressed_u_family,
                compressed_v_family=compressed_v_family,
                compressed_t_v_outside=compressed_t_v_outside,
                compressed_image_of_t_v_outside=compressed_image_of_t_v_outside,
                delta_before=delta_before,
                delta_after=delta_after,
            )
    return None


def max_destroyed_rank4_targets_by_available_rank3_sets_with_witness(
    target_rank4_sets: Sequence[int], available_rank3_sets: Sequence[int], budget: int
) -> Tuple[int, Tuple[int, ...]]:
    triple_index = {subset: index for index, subset in enumerate(available_rank3_sets)}
    target_masks: List[int] = []
    for rank4_set in target_rank4_sets:
        triple_mask = 0
        valid_target = True
        candidates = rank4_set
        while candidates:
            bit = candidates & -candidates
            triple = rank4_set ^ bit
            triple_position = triple_index.get(triple)
            if triple_position is None:
                valid_target = False
                break
            triple_mask |= 1 << triple_position
            candidates ^= bit
        if valid_target:
            target_masks.append(triple_mask)
    dp: Dict[int, int] = {0: 0}
    for target_mask in target_masks:
        updates: Dict[int, int] = {}
        for union_mask, destroyed in dp.items():
            new_union_mask = union_mask | target_mask
            if new_union_mask.bit_count() > budget:
                continue
            candidate_destroyed = destroyed + 1
            current = max(dp.get(new_union_mask, -1), updates.get(new_union_mask, -1))
            if candidate_destroyed > current:
                updates[new_union_mask] = candidate_destroyed
        for union_mask, destroyed in updates.items():
            current = dp.get(union_mask)
            if current is None or current < destroyed:
                dp[union_mask] = destroyed
    best_union_mask, best_destroyed = max(
        dp.items(), key=lambda item: (item[1], -item[0].bit_count(), item[0])
    )
    witness = tuple(
        available_rank3_sets[index]
        for index in range(len(available_rank3_sets))
        if best_union_mask & (1 << index)
    )
    return (best_destroyed, witness)


def exact_min_prism_boundary_in_rank3_removal_model(
    family_n: Family, subsets: Sequence[int]
) -> Tuple[int, int, int]:
    ambient_dimension = max((subset.bit_length() for subset in subsets), default=0)
    lower_half = set(lower_half_family(ambient_dimension, subsets))
    family_n_set = set(family_n)
    upper_part = tuple(sorted(family_n_set - lower_half))
    excess = len(upper_part)
    outside_rank4_sets = [
        subset
        for subset in subsets
        if subset_cardinality(subset) == 4 and subset not in family_n_set
    ]
    all_rank3_sets = [subset for subset in subsets if subset_cardinality(subset) == 3]
    best_boundary: int | None = None
    best_upper_downset_size = 0
    best_destroyed = 0
    for upper_downset in upper_downsets(upper_part):
        support_rank3 = support_rank3_sets_of_upper_downset(upper_downset)
        removal_budget = excess + len(upper_downset)
        available_rank3_sets = [
            rank3_set for rank3_set in all_rank3_sets if rank3_set not in support_rank3
        ]
        if removal_budget > len(available_rank3_sets):
            continue
        killed_outside_rank4 = max_destroyed_rank4_targets_by_available_rank3_sets(
            outside_rank4_sets, available_rank3_sets, removal_budget
        )
        min_boundary = (
            len(upper_part) - len(upper_downset)
            + removal_budget
            + (len(outside_rank4_sets) - killed_outside_rank4)
            + outside_high_boundary_count_from_upper_downset(upper_downset, family_n_set, subsets)
        )
        if best_boundary is None or min_boundary < best_boundary:
            best_boundary = min_boundary
            best_upper_downset_size = len(upper_downset)
            best_destroyed = killed_outside_rank4
    if best_boundary is None:
        return (0, 0, 0)
    return (best_boundary, best_upper_downset_size, best_destroyed)


def simple_lower_generator_classes_n7_exact() -> List[Tuple[str, Tuple[int, ...]]]:
    n = 7
    subsets = all_subsets(n)
    lower_half = set(lower_half_family(n, subsets))
    classes: List[Tuple[str, Tuple[int, ...]]] = []
    seen_families: Set[Family] = set()

    for rank in range(4, 8):
        generators = (initial_segment_mask(rank),)
        family_n = downset_from_generators_above_lower_half(n, subsets, generators)
        upper_part = tuple(sorted(set(family_n) - lower_half))
        if len(upper_part) > 12 or family_n in seen_families:
            continue
        classes.append((f"single-{rank}", generators))
        seen_families.add(family_n)

    for left_rank in range(4, 8):
        for right_rank in range(left_rank, 8):
            min_intersection = max(0, left_rank + right_rank - n)
            for intersection in range(min_intersection, min(left_rank, right_rank) + 1):
                if left_rank == right_rank and intersection == left_rank:
                    continue
                generators = representative_pair_generators(
                    n, left_rank, right_rank, intersection
                )
                family_n = downset_from_generators_above_lower_half(n, subsets, generators)
                upper_part = tuple(sorted(set(family_n) - lower_half))
                if len(upper_part) > 12 or family_n in seen_families:
                    continue
                name = f"pair-{left_rank}-{right_rank}-int{intersection}"
                classes.append((name, generators))
                seen_families.add(family_n)

    return classes


def structured_upper_tail_prism_gap_results_n7_simple_lower() -> List[StructuredUpperTailPrismGapResult]:
    n = 7
    m = n // 2
    subsets = all_subsets(n)
    lower_half = set(lower_half_family(n, subsets))
    target = comb(n + 1, m + 1)
    generator_classes = [
        ("single-5", (31,)),
        ("pair-5-int4", (31, 47)),
        ("pair-5-int3", (31, 103)),
        ("single-6", (63,)),
    ]
    results: List[StructuredUpperTailPrismGapResult] = []
    for name, generators in generator_classes:
        family_n = downset_from_generators_above_lower_half(n, subsets, generators)
        upper_part = set(family_n) - lower_half
        excess = len(upper_part)
        upper_boundary = positive_boundary(family_n, subsets)
        outside_support_ranks = tuple(
            rank
            for rank in range(n + 1)
            if (rank <= m or m + 3 <= rank) and slice_cardinality(upper_boundary, rank) > 0
        )
        upper_total_size = total_size(tuple(sorted(upper_part)))
        exact_upper_downset_search = len(upper_part) <= 12
        if exact_upper_downset_search:
            min_interface_boundary, best_upper_downset_size, best_destroyed = (
                exact_min_prism_boundary_in_rank3_removal_model(family_n, subsets)
            )
            min_prism_boundary = len(upper_boundary) + min_interface_boundary
        else:
            upper_rank4_sets = [subset for subset in upper_part if subset_cardinality(subset) == 4]
            target_rank4_sets = [
                subset
                for subset in subsets
                if subset_cardinality(subset) == 4 and subset not in upper_part
            ]
            best_destroyed = max_destroyed_rank4_targets_by_rank3_budget(
                n, subsets, target_rank4_sets, excess
            )
            best_upper_downset_size = 0
            min_prism_boundary = (
                len(upper_boundary)
                + len(upper_part)
                + excess
                + (35 - len(upper_rank4_sets) - best_destroyed)
            )
        results.append(
            StructuredUpperTailPrismGapResult(
                name=name,
                n=n,
                e=excess,
                target=target,
                exact_upper_downset_search=exact_upper_downset_search,
                best_upper_downset_size=best_upper_downset_size,
                upper_total_size_gain_over_simple_lower_budget=upper_total_size - 4 * excess,
                upper_boundary_size=len(upper_boundary),
                outside_support_ranks=outside_support_ranks,
                best_destroyed_outside_rank4=best_destroyed,
                min_prism_boundary=min_prism_boundary,
            )
        )
    return results


def structured_first_gap_defect_results_n7_simple_lower() -> List[StructuredFirstGapDefectResult]:
    n = 7
    m = n // 2
    subsets = all_subsets(n)
    lower_half = set(lower_half_family(n, subsets))
    target = 2 * comb(n, m)
    results: List[StructuredFirstGapDefectResult] = []
    for name, generators in simple_lower_generator_classes_n7_exact():
        family_n = downset_from_generators_above_lower_half(n, subsets, generators)
        upper_part = tuple(sorted(set(family_n) - lower_half))
        upper_boundary = positive_boundary(family_n, subsets)
        min_interface_boundary, best_upper_downset_size, best_destroyed = (
            exact_min_prism_boundary_in_rank3_removal_model(family_n, subsets)
        )
        upper_profile = tuple(
            slice_cardinality(upper_part, rank) for rank in range(m + 1, n + 1)
        )
        weighted_upper_tail_gain = sum(
            (rank - (m + 1)) * slice_cardinality(upper_part, rank)
            for rank in range(m + 2, n + 1)
        )
        results.append(
            StructuredFirstGapDefectResult(
                name=name,
                n=n,
                e=len(upper_part),
                target=target,
                upper_profile=upper_profile,
                weighted_upper_tail_gain=weighted_upper_tail_gain,
                exact_upper_downset_search=True,
                best_upper_downset_size=best_upper_downset_size,
                upper_boundary_size=len(upper_boundary),
                best_destroyed_outside_rank4=best_destroyed,
                min_prism_boundary=len(upper_boundary) + min_interface_boundary,
            )
        )
    return sorted(
        results,
        key=lambda result: (
            result.weighted_upper_tail_gain,
            result.min_prism_boundary,
            result.e,
            result.name,
        ),
    )


def structured_uniform_upper_middle_layer_results_n7() -> List[StructuredUniformUpperMiddleLayerResult]:
    n = 7
    subsets = all_subsets(n)
    lower_half = set(lower_half_family(n, subsets))
    all_rank3_sets = rank_subsets(n, 3, subsets)
    all_rank4_sets = rank_subsets(n, 4, subsets)
    results: List[StructuredUniformUpperMiddleLayerResult] = []
    for name, generators in simple_lower_generator_classes_n7_exact():
        family_n = downset_from_generators_above_lower_half(n, subsets, generators)
        upper_part = tuple(sorted(set(family_n) - lower_half))
        if any(subset_cardinality(subset) != 4 for subset in upper_part):
            continue
        upper_shadow = upper_shadow_of_uniform_middle_family(upper_part, subsets)
        outside_rank4_targets = [
            subset for subset in all_rank4_sets if subset not in set(upper_part)
        ]
        max_t_v_outside, best_v = max_destroyed_rank4_targets_by_available_rank3_sets_with_witness(
            outside_rank4_targets, all_rank3_sets, len(upper_part)
        )
        best_t_v_outside = tuple(
            subset
            for subset in outside_rank4_targets
            if all((subset ^ bit) in set(best_v) for bit in (1 << i for i in range(subset.bit_length()) if subset & (1 << i)))
        )
        results.append(
            StructuredUniformUpperMiddleLayerResult(
                name=name,
                n=n,
                e=len(upper_part),
                upper_shadow_size=len(upper_shadow),
                max_t_v_outside=max_t_v_outside,
                reduced_margin=len(upper_shadow) - max_t_v_outside,
                best_v=tuple(sorted(best_v)),
                best_t_v_outside=tuple(sorted(best_t_v_outside)),
            )
        )
    return sorted(results, key=lambda result: (result.reduced_margin, result.e, result.name))


def colex_uniform_upper_middle_layer_results(n: int) -> List[ColexUniformUpperMiddleLayerResult]:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank = middle
    upper_rank = middle + 1
    all_rank_lower_sets = rank_subsets(n, lower_rank, subsets)
    all_rank_upper_sets = rank_subsets(n, upper_rank, subsets)
    results: List[ColexUniformUpperMiddleLayerResult] = []
    for e in range(1, len(all_rank_upper_sets) + 1):
        u_family = colex_initial_segment(n, upper_rank, e, subsets)
        v_family = colex_initial_segment(n, lower_rank, e, subsets)
        upper_shadow = upper_shadow_of_uniform_middle_family(u_family, subsets)
        t_v = t_of_v_family(v_family, subsets)
        t_v_outside = tuple(subset for subset in t_v if subset not in set(u_family))
        results.append(
            ColexUniformUpperMiddleLayerResult(
                n=n,
                e=e,
                upper_shadow_size=len(upper_shadow),
                t_v_size=len(t_v),
                t_v_outside_size=len(t_v_outside),
                reduced_margin=len(upper_shadow) - len(t_v_outside),
            )
        )
    return results


def summarize_colex_uniform_upper_middle_layer(n: int) -> ColexUniformUpperMiddleLayerSummary:
    results = colex_uniform_upper_middle_layer_results(n)
    worst_reduced_margin_result = min(
        results, key=lambda result: (result.reduced_margin, result.e)
    )
    worst_t_v_outside_result = max(
        results, key=lambda result: (result.t_v_outside_size, -result.e)
    )
    return ColexUniformUpperMiddleLayerSummary(
        n=n,
        all_reduced_margins_nonnegative=all(result.reduced_margin >= 0 for result in results),
        all_t_v_outside_zero=all(result.t_v_outside_size == 0 for result in results),
        worst_reduced_margin=worst_reduced_margin_result.reduced_margin,
        worst_reduced_margin_e=worst_reduced_margin_result.e,
        max_t_v_outside_size=worst_t_v_outside_result.t_v_outside_size,
        max_t_v_outside_e=worst_t_v_outside_result.e,
        sample_count=len(results),
    )


def search_pair_interface_counterexample(
    n: int,
    downsets: Sequence[Family],
    boundary_cache: Dict[Family, Set[int]],
    max_excess: int,
) -> PairInterfaceCounterexample | None:
    half = 2 ** (n - 1)
    target = 2 * comb(n, n // 2)
    by_size: Dict[int, List[Family]] = {}
    for family in downsets:
        by_size.setdefault(len(family), []).append(family)
    for excess in range(0, min(half, max_excess) + 1):
        large_size = half + excess
        small_size = half - excess
        for family_n in by_size.get(large_size, []):
            family_n_set = set(family_n)
            boundary_n = boundary_cache[family_n]
            for family_m in by_size.get(small_size, []):
                family_m_set = set(family_m)
                if not family_m_set.issubset(family_n_set):
                    continue
                lhs = len(boundary_n) + len((family_n_set - family_m_set) | boundary_cache[family_m])
                if lhs < target:
                    return PairInterfaceCounterexample(
                        n=n,
                        e=excess,
                        target=target,
                        lhs=lhs,
                        family_n=family_n,
                        family_m=family_m,
                    )
    return None


def pair_interface_minima(
    n: int,
    downsets: Sequence[Family],
    boundary_cache: Dict[Family, Set[int]],
    max_excess: int,
) -> List[Tuple[int, int]]:
    half = 2 ** (n - 1)
    by_size: Dict[int, List[Family]] = {}
    for family in downsets:
        by_size.setdefault(len(family), []).append(family)
    minima: List[Tuple[int, int]] = []
    for excess in range(0, min(half, max_excess) + 1):
        large_size = half + excess
        small_size = half - excess
        best: int | None = None
        for family_n in by_size.get(large_size, []):
            family_n_set = set(family_n)
            boundary_n = boundary_cache[family_n]
            for family_m in by_size.get(small_size, []):
                family_m_set = set(family_m)
                if not family_m_set.issubset(family_n_set):
                    continue
                lhs = len(boundary_n) + len((family_n_set - family_m_set) | boundary_cache[family_m])
                if best is None or lhs < best:
                    best = lhs
        if best is not None:
            minima.append((excess, best))
    return minima


def search_upper_tail_prism_gap_counterexample(
    n: int,
    downsets: Sequence[Family],
    boundary_cache: Dict[Family, Set[int]],
    max_excess: int,
) -> UpperTailPrismGapCounterexample | None:
    half = 2 ** (n - 1)
    m = n // 2
    target = comb(n + 1, m + 1)
    witness_total_size = even_lower_half_total_size_in_prism_dimension(n)
    by_size: Dict[int, List[Family]] = {}
    family_set_cache = {family: set(family) for family in downsets}
    total_size_cache = {family: total_size(family) for family in downsets}
    for family in downsets:
        by_size.setdefault(len(family), []).append(family)
    for excess in range(1, min(half, max_excess) + 1):
        large_size = half + excess
        small_size = half - excess
        for family_n in by_size.get(large_size, []):
            boundary_n = boundary_cache[family_n]
            outside_rank: int | None = None
            for rank in range(n + 1):
                if rank > m and rank < m + 3:
                    continue
                if slice_cardinality(boundary_n, rank) > 0:
                    outside_rank = rank
                    break
            if outside_rank is None:
                continue
            family_n_set = family_set_cache[family_n]
            family_n_total_size = total_size_cache[family_n]
            for family_m in by_size.get(small_size, []):
                family_m_set = family_set_cache[family_m]
                if not family_m_set.issubset(family_n_set):
                    continue
                prism_total_size = family_n_total_size + total_size_cache[family_m] + len(family_m)
                if prism_total_size <= witness_total_size:
                    continue
                prism_boundary_size = len(boundary_n) + len(
                    (family_n_set - family_m_set) | boundary_cache[family_m]
                )
                if prism_boundary_size <= target:
                    return UpperTailPrismGapCounterexample(
                        n=n,
                        e=excess,
                        target=target,
                        boundary_size=prism_boundary_size,
                        witness_total_size=witness_total_size,
                        prism_total_size=prism_total_size,
                        outside_rank=outside_rank,
                        family_n=family_n,
                        family_m=family_m,
                    )
    return None


def half_cube_slice_minima(n: int, downsets: Sequence[Family]) -> List[int]:
    half = 2 ** (n - 1)
    half_cube_families = [family for family in downsets if len(family) == half]
    minima: List[int] = []
    for rank in range(n + 1):
        best = min(
            sum(1 for subset in family if subset_cardinality(subset) == rank)
            for family in half_cube_families
        )
        minima.append(best)
    return minima


def truncated_even_binomial_target(n: int) -> List[int]:
    midpoint = n // 2
    return [comb(n - 1, rank) if rank <= midpoint else 0 for rank in range(n + 1)]


def odd_lower_half_target(n: int) -> List[int]:
    midpoint = n // 2
    return [comb(n, rank) if rank <= midpoint else 0 for rank in range(n + 1)]


def boundary_minimizer_slice_profiles(
    n: int, downsets: Sequence[Family], boundary_cache: Dict[Family, Set[int]]
) -> Tuple[int, List[Tuple[int, ...]]]:
    half = 2 ** (n - 1)
    half_cube_families = [family for family in downsets if len(family) == half]
    min_boundary = min(len(boundary_cache[family]) for family in half_cube_families)
    profiles = sorted(
        {
            tuple(
                sum(1 for subset in family if subset_cardinality(subset) == rank)
                for rank in range(n + 1)
            )
            for family in half_cube_families
            if len(boundary_cache[family]) == min_boundary
        }
    )
    return min_boundary, profiles


def search_minimal_outside_counterexample(
    n: int,
    downsets: Sequence[Family],
    minimal_outside_cache: Dict[Family, Set[int]],
) -> MinimalOutsideCounterexample | None:
    half = 2 ** (n - 1)
    middle = comb(n, n // 2)
    best_family: Family | None = None
    best_minimal_outside: Family = ()
    best_size: int | None = None
    for family in downsets:
        if len(family) != half:
            continue
        current_minimal_outside = tuple(sorted(minimal_outside_cache[family]))
        current_size = len(current_minimal_outside)
        if best_size is None or current_size < best_size:
            best_size = current_size
            best_family = family
            best_minimal_outside = current_minimal_outside
    if best_size is None or best_family is None or best_size >= middle:
        return None
    return MinimalOutsideCounterexample(
        n=n,
        middle=middle,
        minimum=best_size,
        family=best_family,
        minimal_outside=best_minimal_outside,
    )


def search_boundary_minimizer_positive_boundary_antichain_failure(
    n: int,
    downsets: Sequence[Family],
    boundary_cache: Dict[Family, Set[int]],
) -> BoundaryAntichainFailure | None:
    half = 2 ** (n - 1)
    middle = comb(n, n // 2)
    half_cube_families = [family for family in downsets if len(family) == half]
    min_boundary = min(len(boundary_cache[family]) for family in half_cube_families)
    for family in half_cube_families:
        boundary = tuple(sorted(boundary_cache[family]))
        if len(boundary) != min_boundary:
            continue
        if len(boundary) != middle or not is_antichain(boundary):
            return BoundaryAntichainFailure(
                n=n,
                boundary_size=len(boundary),
                middle=middle,
                family=family,
                boundary=boundary,
            )
    return None


def analyze_dimension(
    n: int, max_excess: int
) -> Tuple[
    List[Tuple[int, int, int]],
    List[int],
    List[int],
    int,
    List[Tuple[int, ...]],
    List[int],
    BoundaryAntichainFailure | None,
    MinimalOutsideCounterexample | None,
    List[Tuple[int, int]],
    PairInterfaceCounterexample | None,
    UpperTailPrismGapCounterexample | None,
]:
    subsets, downsets = enumerate_downsets(n)
    boundary_cache = {family: positive_boundary(family, subsets) for family in downsets}
    minimal_outside_cache = {family: minimal_outside(family, subsets) for family in downsets}
    profiles = profile_table(n, downsets, boundary_cache, max_excess)
    slice_minima = half_cube_slice_minima(n, downsets)
    slice_target = truncated_even_binomial_target(n)
    extremal_boundary, extremal_profiles = boundary_minimizer_slice_profiles(
        n, downsets, boundary_cache
    )
    extremal_target = odd_lower_half_target(n)
    boundary_antichain_bad = search_boundary_minimizer_positive_boundary_antichain_failure(
        n, downsets, boundary_cache
    )
    min_out_bad = search_minimal_outside_counterexample(n, downsets, minimal_outside_cache)
    pair_min = pair_interface_minima(n, downsets, boundary_cache, max_excess)
    bad = search_pair_interface_counterexample(n, downsets, boundary_cache, max_excess)
    upper_tail_bad = search_upper_tail_prism_gap_counterexample(
        n, downsets, boundary_cache, max_excess
    )
    return (
        profiles,
        slice_minima,
        slice_target,
        extremal_boundary,
        extremal_profiles,
        extremal_target,
        boundary_antichain_bad,
        min_out_bad,
        pair_min,
        bad,
        upper_tail_bad,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Exhaustive low-dimensional search for the odd-cube boundary program in Problem #1."
    )
    parser.add_argument(
        "--structured-upper-tail-n7-simple-lower",
        action="store_true",
        help=(
            "Run the exact structured n=7 falsification search for the upper-tail prism gap "
            "in the class N = lower_half + small high-rank generators, "
            "M = lower_half minus e rank-3 sets."
        ),
    )
    parser.add_argument(
        "--structured-first-gap-defect-n7-simple-lower",
        action="store_true",
        help=(
            "Run the exact structured n=7 first-gap defect search in the simple-lower model "
            "over single/pair generator orbit classes with upper part size at most 12."
        ),
    )
    parser.add_argument(
        "--structured-uniform-upper-middle-layer-n7",
        action="store_true",
        help=(
            "Run the exact structured n=7 search for the reduced middle-layer inequality "
            "|∂^up U| >= |T(V) \\ U| on uniform-upper simple-lower classes."
        ),
    )
    parser.add_argument(
        "--colex-uniform-upper-middle-layer-n7",
        action="store_true",
        help=(
            "Tabulate the reduced middle-layer quantity |∂^up U| - |T(V) \\ U| "
            "for colex-initial rank-4/rank-3 segments in n=7."
        ),
    )
    parser.add_argument(
        "--colex-uniform-upper-middle-layer-odd-dimensions",
        type=int,
        nargs="+",
        help=(
            "Summarize the colex compressed middle-layer inequality on the given odd dimensions. "
            "For each odd n, report whether all colex equal-size middle-layer pairs satisfy "
            "T(V*) \\ U* = ∅ and the reduced inequality."
        ),
    )
    parser.add_argument(
        "--middle-layer-compression-counterexample-n7",
        action="store_true",
        help=(
            "Exhibit the canonical n=7 counterexample to the strong compression inclusion "
            "C_ij(T(V) \\ U) ⊆ T(C_ij V) \\ C_ij U, and test the weaker Δ-monotonicity on the "
            "same canonical V."
        ),
    )
    parser.add_argument(
        "--exhaustive-colex-defect-reduction-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the weaker colex-reduction theorem for "
            "Δ(U,V)=|T(V)\\\\U|-|∂^up U|. This checks whether every equal-size middle-layer pair "
            "is dominated by the equal-size colex pair."
        ),
    )
    parser.add_argument(
        "--dimensions",
        type=int,
        nargs="+",
        default=[1, 3, 5],
        help="Odd dimensions to search. Defaults to 1 3 5.",
    )
    parser.add_argument(
        "--max-excess",
        type=int,
        default=8,
        help="How far above half-cube size to tabulate the odd excess profile.",
    )
    args = parser.parse_args()

    if args.structured_upper_tail_n7_simple_lower:
        any_warning = False
        for result in structured_upper_tail_prism_gap_results_n7_simple_lower():
            if result.outside_support_ranks and result.upper_total_size_gain_over_simple_lower_budget > 0:
                if result.min_prism_boundary <= result.target:
                    any_warning = True
                    warn(
                        "WARNING structured upper-tail prism gap counterexample found in class "
                        f"{result.name}: min_boundary={result.min_prism_boundary} <= target={result.target}"
                    )
                else:
                    ok(
                        "OK structured n=7 class "
                        f"{result.name}: min_boundary={result.min_prism_boundary} > target={result.target}"
                    )
            else:
                ok(
                    "OK structured n=7 class "
                    f"{result.name}: hypotheses already fail before the boundary test"
                )
            print(
                f"  e={result.e} gain={result.upper_total_size_gain_over_simple_lower_budget} "
                f"exact_upper_search={result.exact_upper_downset_search} "
                f"best_upper_size={result.best_upper_downset_size} "
                f"outside_support={list(result.outside_support_ranks)} "
                f"upper_boundary={result.upper_boundary_size} "
                f"best_destroyed_outside_rank4={result.best_destroyed_outside_rank4}"
            )
        if any_warning:
            warn("WARNING overall: structured n=7 upper-tail search found a candidate.")
            return 1
        ok("OK overall: no structured n=7 simple-lower upper-tail counterexample found.")
        return 0

    if args.structured_first_gap_defect_n7_simple_lower:
        any_warning = False
        results = structured_first_gap_defect_results_n7_simple_lower()
        for result in results:
            boundary_margin = result.min_prism_boundary - result.target
            if result.min_prism_boundary <= result.target:
                any_warning = True
                warn(
                    "WARNING structured n=7 first-gap defect candidate found in class "
                    f"{result.name}: min_boundary={result.min_prism_boundary} <= target={result.target}"
                )
            else:
                ok(
                    "OK structured n=7 first-gap class "
                    f"{result.name}: min_boundary={result.min_prism_boundary} > target={result.target}"
                )
            print(
                f"  e={result.e} upper_profile={list(result.upper_profile)} "
                f"weighted_gain={result.weighted_upper_tail_gain} "
                f"boundary_margin={boundary_margin} "
                f"best_upper_size={result.best_upper_downset_size} "
                f"upper_boundary={result.upper_boundary_size} "
                f"best_destroyed_outside_rank4={result.best_destroyed_outside_rank4}"
            )
        zero_gain_results = [
            result for result in results if result.weighted_upper_tail_gain == 0
        ]
        if zero_gain_results:
            tightest_zero_gain = min(
                zero_gain_results, key=lambda result: result.min_prism_boundary
            )
            print(
                "TIGHTEST zero-gain class: "
                f"{tightest_zero_gain.name} with min_boundary={tightest_zero_gain.min_prism_boundary} "
                f"(target={tightest_zero_gain.target}, margin={tightest_zero_gain.min_prism_boundary - tightest_zero_gain.target})"
            )
        tightest_overall = min(results, key=lambda result: result.min_prism_boundary)
        print(
            "TIGHTEST overall exact class: "
            f"{tightest_overall.name} with upper_profile={list(tightest_overall.upper_profile)} "
            f"weighted_gain={tightest_overall.weighted_upper_tail_gain} "
            f"min_boundary={tightest_overall.min_prism_boundary} "
            f"(target={tightest_overall.target}, margin={tightest_overall.min_prism_boundary - tightest_overall.target})"
        )
        if any_warning:
            warn("WARNING overall: structured n=7 first-gap defect search found a candidate.")
            return 1
        ok(
            "OK overall: no exact structured n=7 simple-lower first-gap defect candidate found."
        )
        return 0

    if args.structured_uniform_upper_middle_layer_n7:
        any_warning = False
        results = structured_uniform_upper_middle_layer_results_n7()
        for result in results:
            if result.reduced_margin < 0:
                any_warning = True
                warn(
                    "WARNING structured n=7 uniform-upper middle-layer failure found in class "
                    f"{result.name}: shadow={result.upper_shadow_size} < Tout={result.max_t_v_outside}"
                )
            else:
                ok(
                    "OK structured n=7 uniform-upper class "
                    f"{result.name}: shadow={result.upper_shadow_size} >= Tout={result.max_t_v_outside}"
                )
            print(
                f"  e={result.e} reduced_margin={result.reduced_margin} "
                f"best_v_size={len(result.best_v)} best_t_v_outside={len(result.best_t_v_outside)}"
            )
            if result.best_v:
                print(f"  best V = {format_family(result.best_v)}")
            if result.best_t_v_outside:
                print(f"  best T(V)\\\\U = {format_family(result.best_t_v_outside)}")
        if any_warning:
            warn("WARNING overall: structured n=7 uniform-upper middle-layer search found a candidate.")
            return 1
        ok("OK overall: no structured n=7 uniform-upper middle-layer counterexample found.")
        return 0

    if args.colex_uniform_upper_middle_layer_n7:
        any_warning = False
        results = colex_uniform_upper_middle_layer_results(7)
        for result in results:
            if result.reduced_margin < 0:
                any_warning = True
                warn(
                    "WARNING colex n=7 middle-layer failure at "
                    f"e={result.e}: shadow={result.upper_shadow_size} < Tout={result.t_v_outside_size}"
                )
            else:
                ok(
                    "OK colex n=7 e="
                    f"{result.e}: shadow={result.upper_shadow_size} >= Tout={result.t_v_outside_size}"
                )
            print(
                f"  T(V)={result.t_v_size} T(V)\\\\U={result.t_v_outside_size} "
                f"reduced_margin={result.reduced_margin}"
            )
        if any_warning:
            warn("WARNING overall: a colex n=7 middle-layer candidate failed.")
            return 1
        ok("OK overall: all colex n=7 middle-layer samples satisfy the reduced inequality.")
        return 0

    if args.colex_uniform_upper_middle_layer_odd_dimensions is not None:
        any_warning = False
        for n in args.colex_uniform_upper_middle_layer_odd_dimensions:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            summary = summarize_colex_uniform_upper_middle_layer(n)
            if not summary.all_reduced_margins_nonnegative:
                any_warning = True
                warn(
                    "WARNING colex odd middle-layer failure at "
                    f"n={n}: worst_reduced_margin={summary.worst_reduced_margin} "
                    f"at e={summary.worst_reduced_margin_e}"
                )
            else:
                ok(
                    "OK colex odd middle-layer reduced inequality at "
                    f"n={n}: worst_reduced_margin={summary.worst_reduced_margin} "
                    f"at e={summary.worst_reduced_margin_e}"
                )
            if summary.all_t_v_outside_zero:
                ok(
                    "OK colex odd middle-layer containment at "
                    f"n={n}: T(V*)\\\\U*=∅ for all e in 1..{summary.sample_count}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING colex odd middle-layer containment fails at "
                    f"n={n}: max T(V*)\\\\U* size={summary.max_t_v_outside_size} "
                    f"at e={summary.max_t_v_outside_e}"
                )
        if any_warning:
            warn("WARNING overall: some requested odd-dimension colex summaries failed.")
            return 1
        ok("OK overall: all requested odd-dimension colex summaries survived.")
        return 0

    if args.middle_layer_compression_counterexample_n7:
        result = canonical_middle_layer_compression_inclusion_counterexample_n7()
        image_set = set(result.compressed_image_of_t_v_outside)
        target_set = set(result.compressed_t_v_outside)
        if image_set.issubset(target_set):
            ok(
                "OK canonical n=7 example: the strong compression inclusion unexpectedly survives."
            )
        else:
            warn(
                "WARNING canonical n=7 example falsifies the strong compression inclusion "
                "C_ij(T(V) \\ U) ⊆ T(C_ij V) \\ C_ij U."
            )
        print(f"  n={result.n} compression=(i,j)=({result.i},{result.j})")
        print(f"  V = {format_family(result.v_family)}")
        print(f"  U = {format_family(result.u_family)}")
        print(f"  T(V)\\\\U = {format_family(result.t_v_outside)}")
        print(f"  C(U) = {format_family(result.compressed_u_family)}")
        print(f"  C(V) = {format_family(result.compressed_v_family)}")
        print(f"  C(T(V)\\\\U) = {format_family(result.compressed_image_of_t_v_outside)}")
        print(f"  T(C(V))\\\\C(U) = {format_family(result.compressed_t_v_outside)}")
        print(
            f"  delta_before={result.delta_before} delta_after={result.delta_after}"
        )

        delta_failure = search_canonical_middle_layer_delta_failure_n7()
        if delta_failure is None:
            ok(
                "OK canonical n=7 e=4 sweep: no Δ-monotonicity failure found for the fixed witness V."
            )
            return 0
        warn(
            "WARNING canonical n=7 e=4 sweep found a Δ-monotonicity failure for the fixed witness V."
        )
        print(f"  failing U = {format_family(delta_failure.u_family)}")
        print(f"  delta_before={delta_failure.delta_before} delta_after={delta_failure.delta_after}")
        return 1

    if args.exhaustive_colex_defect_reduction_n5:
        result = exhaustive_colex_defect_reduction_failure(5)
        if result is None:
            ok(
                "OK exact n=5: the weaker colex defect-reduction theorem survives exhaustive search."
            )
            return 0
        warn("WARNING exact n=5: the weaker colex defect-reduction theorem fails.")
        print(
            f"  e={result.e} colex_delta={result.colex_delta} witness_delta={result.witness_delta}"
        )
        print(f"  colex U* = {format_family(result.colex_u_family)}")
        print(f"  colex V* = {format_family(result.colex_v_family)}")
        print(f"  witness U = {format_family(result.witness_u_family)}")
        print(f"  witness V = {format_family(result.witness_v_family)}")
        return 1

    dimensions = tuple(args.dimensions)
    total_steps = len(dimensions) * 8
    completed = 0
    any_warning = False

    for n in dimensions:
        render_progress(completed, total_steps, f"enumerating odd-cube data for n={n}")
        (
            profiles,
            slice_minima,
            slice_target,
            extremal_boundary,
            extremal_profiles,
            extremal_target,
            boundary_antichain_bad,
            min_out_bad,
            pair_minima_table,
            bad,
            upper_tail_bad,
        ) = analyze_dimension(n, args.max_excess)
        completed += 1
        render_progress(completed, total_steps, f"computed profile minima for n={n}")

        half = 2 ** (n - 1)
        middle = comb(n, n // 2)
        if extremal_boundary < middle:
            any_warning = True
            warn(
                f"WARNING n={n}: odd half-cube bound fails, min boundary {extremal_boundary} < middle {middle}"
            )
        else:
            ok(
                f"OK n={n}: odd half-cube bound survives search, min boundary {extremal_boundary} >= middle {middle}"
            )

        completed += 1
        render_progress(completed, total_steps, f"checked half-cube slice minima for n={n}")

        if slice_minima != slice_target:
            any_warning = True
            warn(
                f"WARNING n={n}: half-cube slice minima {slice_minima} do not match target {slice_target}"
            )
        else:
            ok(
                f"OK n={n}: half-cube slice minima match truncated even-binomial profile {slice_target}"
            )

        completed += 1
        render_progress(completed, total_steps, f"checked half-cube boundary minimizers for n={n}")

        expected_profile = [tuple(extremal_target)]
        if extremal_profiles != expected_profile:
            any_warning = True
            warn(
                f"WARNING n={n}: half-cube boundary minimizer slice profiles "
                f"{extremal_profiles} do not match odd lower-half target {extremal_target}"
            )
        else:
            ok(
                f"OK n={n}: half-cube boundary minimizers have odd lower-half profile {extremal_target}"
            )

        completed += 1
        render_progress(
            completed, total_steps, f"checked minimizer boundary antichain candidate for n={n}"
        )

        if boundary_antichain_bad is not None:
            any_warning = True
            warn(
                f"WARNING n={n}: boundary minimizer positive boundary is not a middle antichain; "
                f"size={boundary_antichain_bad.boundary_size}, middle={boundary_antichain_bad.middle}"
            )
            print(f"  D = {format_family(boundary_antichain_bad.family)}")
            print(f"  positiveBoundary(D) = {format_family(boundary_antichain_bad.boundary)}")
        else:
            ok(
                f"OK n={n}: every searched half-cube boundary minimizer has middle-sized antichain positive boundary."
            )

        completed += 1
        render_progress(completed, total_steps, f"checked minimalOutside frontier for n={n}")

        if min_out_bad is not None:
            any_warning = True
            warn(
                f"WARNING n={n}: universal minimalOutside bound fails, "
                f"min minimalOutside={min_out_bad.minimum} < middle={min_out_bad.middle}"
            )
            print(f"  D = {format_family(min_out_bad.family)}")
            print(f"  minimalOutside(D) = {format_family(min_out_bad.minimal_outside)}")
        else:
            ok(f"OK n={n}: universal minimalOutside bound survives search.")

        completed += 1
        render_progress(completed, total_steps, f"checked pair-interface candidate for n={n}")

        if bad is not None:
            any_warning = True
            warn(
                "WARNING pair-interface counterexample found at "
                f"n={bad.n}, e={bad.e}: lhs={bad.lhs} < target={bad.target}"
            )
            print(f"  N = {format_family(bad.family_n)}")
            print(f"  M = {format_family(bad.family_m)}")
        else:
            target = 2 * middle
            ok(
                f"OK n={n}: no pair-interface counterexample found up to e={min(half, args.max_excess)}, target={target}"
            )

        completed += 1
        render_progress(completed, total_steps, f"checked upper-tail prism gap candidate for n={n}")

        if upper_tail_bad is not None:
            any_warning = True
            warn(
                "WARNING upper-tail prism gap counterexample found at "
                f"n={upper_tail_bad.n}, e={upper_tail_bad.e}, outside_rank={upper_tail_bad.outside_rank}: "
                f"boundary={upper_tail_bad.boundary_size} <= target={upper_tail_bad.target}"
            )
            print(
                "  prism_total_size="
                f"{upper_tail_bad.prism_total_size} > witness_total_size={upper_tail_bad.witness_total_size}"
            )
            print(f"  N = {format_family(upper_tail_bad.family_n)}")
            print(f"  M = {format_family(upper_tail_bad.family_m)}")
        else:
            target = comb(n + 1, n // 2 + 1)
            ok(
                f"OK n={n}: no upper-tail prism gap counterexample found up to e={min(half, args.max_excess)}, target={target}"
            )

        print(f"n={n} half-cube slice minima:")
        for rank, (minimum, target) in enumerate(zip(slice_minima, slice_target, strict=True)):
            print(f"  r={rank:>2} min_slice={minimum} target={target}")
        print(f"n={n} half-cube boundary minimizer slice profiles (min boundary {extremal_boundary}):")
        for profile in extremal_profiles:
            print(f"  profile={list(profile)} target={extremal_target}")
        print(f"n={n} odd excess profile near half cube:")
        for size, excess, min_boundary in profiles:
            print(f"  size={size:>2} e={excess:>2} min_boundary={min_boundary}")
        print(f"n={n} pair-interface minima:")
        for excess, minimum in pair_minima_table:
            print(f"  e={excess:>2} min_pair_interface={minimum}")
        print()

        completed += 1
        render_progress(completed, total_steps, f"finished n={n}")

    if any_warning:
        warn("WARNING overall: at least one searched candidate failed.")
        return 1
    ok("OK overall: searched odd-dimensional candidates survived on the requested dimensions.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
