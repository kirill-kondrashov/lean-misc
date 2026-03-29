#!/usr/bin/env python3

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations
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
class ExhaustiveTwoLayerBoundaryResult:
    n: int
    e: int
    boundary_size: int
    c_size: int
    margin: int
    witness_u_family: Family
    witness_v_family: Family


@dataclass(frozen=True)
class ExhaustiveTwoLayerHallShadowResult:
    n: int
    e: int
    upper_shadow_size: int
    damaged_u_size: int
    margin: int
    witness_u_family: Family
    witness_v_family: Family


@dataclass(frozen=True)
class ExhaustiveTwoLayerShiftedRouteResult:
    n: int
    e: int
    minimal_boundary_size: int
    lex_shifted_boundary_size: int
    lex_shifted_gap: int
    has_shifted_minimizer: bool
    shifted_witness_c_family: Family | None
    shifted_witness_u_family: Family | None


@dataclass(frozen=True)
class ExhaustiveTwoLayerMinimizerOrbitResult:
    n: int
    e: int
    minimal_boundary_size: int
    minimizer_count: int
    orbit_count: int
    all_minimizers_in_lex_orbit: bool


@dataclass(frozen=True)
class ExhaustiveTwoLayerCompressionCounterexample:
    n: int
    e: int
    i: int
    j: int
    boundary_before: int
    boundary_after: int
    c_family: Family
    u_family: Family
    compressed_c_family: Family
    compressed_u_family: Family


@dataclass(frozen=True)
class ExhaustiveShiftedTwoLayerExtremizerResult:
    n: int
    e: int
    minimal_boundary_size: int
    minimal_margin: int
    shifted_minimizer_count: int
    shifted_minimizer_orbit_count: int
    equality_count: int
    equality_orbit_count: int
    witness_c_family: Family
    witness_u_family: Family


@dataclass(frozen=True)
class ShiftedUniformFamilyCountResult:
    n: int
    rank: int
    family_count: int


@dataclass(frozen=True)
class ExhaustiveShiftedTwoLayerSummaryResult:
    n: int
    lower_shifted_family_count: int
    upper_shifted_family_count: int
    all_margins_nonnegative: bool
    worst_margin: int
    worst_margin_e: int
    equality_count: int


@dataclass(frozen=True)
class ShiftedTwoLayerEqualityOrbitResult:
    n: int
    e: int
    c_family: Family
    u_family: Family


@dataclass(frozen=True)
class ExhaustiveShiftedEvenAdjacentLayerSummaryResult:
    n: int
    r: int
    lower_shifted_family_count: int
    upper_shifted_family_count: int
    all_margins_nonnegative: bool
    worst_margin: int
    equality_count: int
    witness_lower_family: Family
    witness_upper_family: Family


@dataclass(frozen=True)
class ShiftedEvenAdjacentLayerEqualityOrbitResult:
    n: int
    r: int
    lower_family: Family
    upper_family: Family


@dataclass(frozen=True)
class ExhaustiveCoupledSectionSummaryResult:
    n: int
    all_margins_nonnegative: bool
    worst_margin: int
    worst_margin_e: int
    equality_count: int
    witness_u_family: Family
    witness_v_family: Family
    witness_a_family: Family
    witness_b_family: Family
    witness_d_family: Family
    witness_e_family: Family


@dataclass(frozen=True)
class ShiftedCoupledSectionSummaryResult:
    n: int
    lower_shifted_family_count: int
    upper_shifted_family_count: int
    all_margins_nonnegative: bool
    worst_margin: int
    worst_margin_e: int
    equality_count: int
    witness_c_family: Family
    witness_u_family: Family
    witness_a_family: Family
    witness_b_family: Family
    witness_d_family: Family
    witness_e_family: Family


@dataclass(frozen=True)
class TwoLayerLocalFluxCounterexample:
    n: int
    e: int
    max_codim: int
    violating_left_family: Family
    violating_neighbor_family: Family
    c_family: Family
    u_family: Family
    boundary_family: Family


@dataclass(frozen=True)
class ShiftedTwoLayerLocalFluxSummaryResult:
    n: int
    max_codim: int
    lower_shifted_family_count: int
    upper_shifted_family_count: int
    all_pairs_have_matching: bool
    worst_deficiency: int
    worst_deficiency_e: int
    witness_c_family: Family
    witness_u_family: Family
    witness_boundary_family: Family


@dataclass(frozen=True)
class LocalFluxEqualSplitSummaryResult:
    n: int
    max_codim: int
    exact_mode: bool
    all_pairs_respect_capacity: bool
    worst_overload: Fraction
    worst_overload_e: int
    witness_c_family: Family
    witness_u_family: Family
    witness_boundary_family: Family
    witness_boundary_point: int | None
    witness_boundary_load: Fraction


@dataclass(frozen=True)
class LocalFluxInverseDegreeSummaryResult:
    n: int
    max_codim: int
    exact_mode: bool
    all_pairs_respect_capacity: bool
    worst_overload: Fraction
    worst_overload_e: int
    witness_c_family: Family
    witness_u_family: Family
    witness_boundary_family: Family
    witness_boundary_point: int | None
    witness_boundary_load: Fraction


@dataclass(frozen=True)
class LocalFluxGreedySummaryResult:
    rule_name: str
    n: int
    max_codim: int
    exact_mode: bool
    all_pairs_have_matching: bool
    worst_deficiency: int
    worst_deficiency_e: int
    witness_c_family: Family
    witness_u_family: Family
    witness_boundary_family: Family
    unmatched_left_family: Family


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


def lex_key(mask: int) -> Tuple[int, ...]:
    return tuple(index for index in range(mask.bit_length()) if mask & (1 << index))


def colex_initial_segment(n: int, rank: int, size: int, subsets: Sequence[int]) -> Family:
    rank_family = rank_subsets(n, rank, subsets)
    ordered = sorted(rank_family, key=colex_key)
    return tuple(ordered[:size])


def lex_initial_segment(n: int, rank: int, size: int, subsets: Sequence[int]) -> Family:
    rank_family = rank_subsets(n, rank, subsets)
    ordered = sorted(rank_family, key=lex_key)
    return tuple(ordered[:size])


def subset_tuple(mask: int) -> Tuple[int, ...]:
    return tuple(index for index in range(mask.bit_length()) if mask & (1 << index))


def shifted_leq(left: int, right: int) -> bool:
    left_tuple = subset_tuple(left)
    right_tuple = subset_tuple(right)
    if len(left_tuple) != len(right_tuple):
        return False
    return all(left_item <= right_item for left_item, right_item in zip(left_tuple, right_tuple))


def enumerate_shifted_uniform_families(n: int, rank: int, subsets: Sequence[int]) -> List[Family]:
    rank_family = rank_subsets(n, rank, subsets)
    order = sorted(rank_family, key=subset_tuple, reverse=True)
    comparable: Dict[int, Set[int]] = {mask: set() for mask in rank_family}
    for left in rank_family:
        for right in rank_family:
            if shifted_leq(left, right) or shifted_leq(right, left):
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
    families: List[Family] = []
    for antichain in antichains:
        family = tuple(
            sorted(
                subset
                for subset in rank_family
                if any(shifted_leq(subset, maximal) for maximal in antichain)
            )
        )
        families.append(family)
    return families


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


def apply_permutation(mask: int, perm: Sequence[int]) -> int:
    image = 0
    for index, target in enumerate(perm):
        if mask & (1 << index):
            image |= 1 << target
    return image


def permute_family(family: Sequence[int], perm: Sequence[int]) -> Family:
    return tuple(sorted(apply_permutation(member, perm) for member in family))


def section_split_at_zero(family: Sequence[int]) -> Tuple[Family, Family]:
    with_zero: List[int] = []
    without_zero: List[int] = []
    for member in family:
        section_member = member >> 1
        if member & 1:
            with_zero.append(section_member)
        else:
            without_zero.append(section_member)
    return tuple(sorted(with_zero)), tuple(sorted(without_zero))


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


def exhaustive_two_layer_middle_boundary_minima(
    n: int,
) -> List[ExhaustiveTwoLayerBoundaryResult]:
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

    boundary_cache: Dict[int, int] = {}

    def two_layer_boundary_size(u_mask: int, v_mask: int) -> int:
        key = (u_mask << lower_count) | v_mask
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        c_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if not (v_mask & (1 << index))
        )
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    results: List[ExhaustiveTwoLayerBoundaryResult] = []
    for e in range(lower_count + 1):
        best_boundary: int | None = None
        best_pair: Tuple[int, int] | None = None
        c_size = lower_count - e
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                boundary_size = two_layer_boundary_size(u_mask, v_mask)
                if best_boundary is None or boundary_size < best_boundary:
                    best_boundary = boundary_size
                    best_pair = (u_mask, v_mask)
        if best_boundary is None or best_pair is None:
            continue
        u_mask, v_mask = best_pair
        witness_u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        witness_v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        results.append(
            ExhaustiveTwoLayerBoundaryResult(
                n=n,
                e=e,
                boundary_size=best_boundary,
                c_size=c_size,
                margin=best_boundary - c_size,
                witness_u_family=witness_u_family,
                witness_v_family=witness_v_family,
            )
        )
    return results


def exhaustive_two_layer_hall_shadow_minima(
    n: int,
) -> List[ExhaustiveTwoLayerHallShadowResult]:
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
    upper_index = {subset: index for index, subset in enumerate(upper_rank_sets)}

    for u_mask in range(1 << upper_count):
        u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        upper_shadow_sizes[u_mask] = len(upper_shadow_of_uniform_middle_family(u_family, subsets))

    for v_mask in range(1 << lower_count):
        v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        t_v_family = t_of_v_family(v_family, subsets)
        t_mask = 0
        for subset in t_v_family:
            t_mask |= 1 << upper_index[subset]
        t_v_masks[v_mask] = t_mask

    results: List[ExhaustiveTwoLayerHallShadowResult] = []
    for e in range(lower_count + 1):
        best_margin: int | None = None
        best_pair: Tuple[int, int] | None = None
        best_shadow = 0
        best_damaged = 0
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            upper_shadow_size = upper_shadow_sizes[u_mask]
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                damaged_u_size = (u_mask & ~t_v_masks[v_mask]).bit_count()
                margin = upper_shadow_size - damaged_u_size
                if best_margin is None or margin < best_margin:
                    best_margin = margin
                    best_pair = (u_mask, v_mask)
                    best_shadow = upper_shadow_size
                    best_damaged = damaged_u_size
        if best_margin is None or best_pair is None:
            continue
        u_mask, v_mask = best_pair
        witness_u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        witness_v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        results.append(
            ExhaustiveTwoLayerHallShadowResult(
                n=n,
                e=e,
                upper_shadow_size=best_shadow,
                damaged_u_size=best_damaged,
                margin=best_margin,
                witness_u_family=witness_u_family,
                witness_v_family=witness_v_family,
            )
        )
    return results


def is_shifted_uniform_family(family: Sequence[int], n: int) -> bool:
    family_tuple = tuple(sorted(family))
    for i in range(n):
        for j in range(i + 1, n):
            if compress_uniform_family(family_tuple, i, j) != family_tuple:
                return False
    return True


def exhaustive_two_layer_shifted_route_diagnostics(
    n: int,
) -> List[ExhaustiveTwoLayerShiftedRouteResult]:
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

    boundary_cache: Dict[int, int] = {}

    def two_layer_boundary_size(u_mask: int, v_mask: int) -> int:
        key = (u_mask << lower_count) | v_mask
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        c_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if not (v_mask & (1 << index))
        )
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    lower_index = {subset: index for index, subset in enumerate(lower_rank_sets)}
    upper_index = {subset: index for index, subset in enumerate(upper_rank_sets)}
    results: List[ExhaustiveTwoLayerShiftedRouteResult] = []

    for e in range(lower_count + 1):
        best_boundary: int | None = None
        has_shifted_minimizer = False
        shifted_witness_c_family: Family | None = None
        shifted_witness_u_family: Family | None = None
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                boundary_size = two_layer_boundary_size(u_mask, v_mask)
                if best_boundary is None or boundary_size < best_boundary:
                    best_boundary = boundary_size
                    has_shifted_minimizer = False
                    shifted_witness_c_family = None
                    shifted_witness_u_family = None
                if boundary_size != best_boundary:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                if is_shifted_uniform_family(c_family, n) and is_shifted_uniform_family(u_family, n):
                    has_shifted_minimizer = True
                    shifted_witness_c_family = c_family
                    shifted_witness_u_family = u_family
        lex_u_family = lex_initial_segment(n, upper_rank, e, subsets)
        lex_c_family = lex_initial_segment(n, lower_rank, lower_count - e, subsets)
        lex_u_mask = 0
        for subset in lex_u_family:
            lex_u_mask |= 1 << upper_index[subset]
        lex_c_mask = 0
        for subset in lex_c_family:
            lex_c_mask |= 1 << lower_index[subset]
        lex_v_mask = ((1 << lower_count) - 1) ^ lex_c_mask
        lex_shifted_boundary = two_layer_boundary_size(lex_u_mask, lex_v_mask)
        if best_boundary is None:
            continue
        results.append(
            ExhaustiveTwoLayerShiftedRouteResult(
                n=n,
                e=e,
                minimal_boundary_size=best_boundary,
                lex_shifted_boundary_size=lex_shifted_boundary,
                lex_shifted_gap=lex_shifted_boundary - best_boundary,
                has_shifted_minimizer=has_shifted_minimizer,
                shifted_witness_c_family=shifted_witness_c_family,
                shifted_witness_u_family=shifted_witness_u_family,
            )
        )
    return results


def exhaustive_two_layer_minimizer_orbit_diagnostics(
    n: int,
) -> List[ExhaustiveTwoLayerMinimizerOrbitResult]:
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

    boundary_cache: Dict[int, int] = {}

    def two_layer_boundary_size(u_mask: int, v_mask: int) -> int:
        key = (u_mask << lower_count) | v_mask
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        u_family = tuple(
            upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
        )
        v_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if v_mask & (1 << index)
        )
        c_family = tuple(
            lower_rank_sets[index] for index in range(lower_count) if not (v_mask & (1 << index))
        )
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    lower_index = {subset: index for index, subset in enumerate(lower_rank_sets)}
    upper_index = {subset: index for index, subset in enumerate(upper_rank_sets)}
    perms = tuple(permutations(range(n)))

    def canonical_orbit_rep(c_family: Family, u_family: Family) -> Tuple[Family, Family]:
        candidates = [
            (permute_family(c_family, perm), permute_family(u_family, perm))
            for perm in perms
        ]
        return min(candidates)

    results: List[ExhaustiveTwoLayerMinimizerOrbitResult] = []
    for e in range(lower_count + 1):
        best_boundary: int | None = None
        minimizers: List[Tuple[Family, Family]] = []
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                boundary_size = two_layer_boundary_size(u_mask, v_mask)
                if best_boundary is None or boundary_size < best_boundary:
                    best_boundary = boundary_size
                    minimizers = []
                if boundary_size != best_boundary:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                minimizers.append((c_family, u_family))
        if best_boundary is None:
            continue
        lex_u_family = lex_initial_segment(n, upper_rank, e, subsets)
        lex_c_family = lex_initial_segment(n, lower_rank, lower_count - e, subsets)
        lex_rep = canonical_orbit_rep(lex_c_family, lex_u_family)
        minimizer_reps = {canonical_orbit_rep(c_family, u_family) for c_family, u_family in minimizers}
        results.append(
            ExhaustiveTwoLayerMinimizerOrbitResult(
                n=n,
                e=e,
                minimal_boundary_size=best_boundary,
                minimizer_count=len(minimizers),
                orbit_count=len(minimizer_reps),
                all_minimizers_in_lex_orbit=(minimizer_reps == {lex_rep}),
            )
        )
    return results


def exhaustive_two_layer_boundary_compression_counterexample(
    n: int,
) -> ExhaustiveTwoLayerCompressionCounterexample | None:
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

    lower_index = {subset: index for index, subset in enumerate(lower_rank_sets)}
    upper_index = {subset: index for index, subset in enumerate(upper_rank_sets)}
    boundary_cache: Dict[int, int] = {}

    def family_from_mask(rank_sets: Sequence[int], mask: int) -> Family:
        return tuple(
            rank_sets[index] for index in range(len(rank_sets)) if mask & (1 << index)
        )

    def mask_from_family(index_map: Dict[int, int], family: Sequence[int]) -> int:
        mask = 0
        for subset in family:
            mask |= 1 << index_map[subset]
        return mask

    def two_layer_boundary_size(c_mask: int, u_mask: int) -> int:
        key = (u_mask << lower_count) | c_mask
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        c_family = family_from_mask(lower_rank_sets, c_mask)
        u_family = family_from_mask(upper_rank_sets, u_mask)
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    for c_mask in range(1 << lower_count):
        c_size = c_mask.bit_count()
        e = lower_count - c_size
        c_family = family_from_mask(lower_rank_sets, c_mask)
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = family_from_mask(upper_rank_sets, u_mask)
            boundary_before = two_layer_boundary_size(c_mask, u_mask)
            for i in range(n):
                for j in range(i + 1, n):
                    compressed_c_family = compress_uniform_family(c_family, i, j)
                    compressed_u_family = compress_uniform_family(u_family, i, j)
                    compressed_c_mask = mask_from_family(lower_index, compressed_c_family)
                    compressed_u_mask = mask_from_family(upper_index, compressed_u_family)
                    boundary_after = two_layer_boundary_size(compressed_c_mask, compressed_u_mask)
                    if boundary_after > boundary_before:
                        return ExhaustiveTwoLayerCompressionCounterexample(
                            n=n,
                            e=e,
                            i=i,
                            j=j,
                            boundary_before=boundary_before,
                            boundary_after=boundary_after,
                            c_family=c_family,
                            u_family=u_family,
                            compressed_c_family=compressed_c_family,
                            compressed_u_family=compressed_u_family,
                        )
    return None


def exhaustive_shifted_two_layer_extremizers(
    n: int,
) -> List[ExhaustiveShiftedTwoLayerExtremizerResult]:
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

    boundary_cache: Dict[int, int] = {}
    perms = tuple(permutations(range(n)))

    def two_layer_boundary_size(c_family: Family, u_family: Family) -> int:
        c_mask = 0
        for index, subset in enumerate(lower_rank_sets):
            if subset in set(c_family):
                c_mask |= 1 << index
        u_mask = 0
        for index, subset in enumerate(upper_rank_sets):
            if subset in set(u_family):
                u_mask |= 1 << index
        key = (u_mask << lower_count) | c_mask
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    def canonical_orbit_rep(c_family: Family, u_family: Family) -> Tuple[Family, Family]:
        candidates = [
            (permute_family(c_family, perm), permute_family(u_family, perm))
            for perm in perms
        ]
        return min(candidates)

    results: List[ExhaustiveShiftedTwoLayerExtremizerResult] = []
    for e in range(lower_count + 1):
        shifted_pairs: List[Tuple[Family, Family, int]] = []
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            if not is_shifted_uniform_family(u_family, n):
                continue
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                if not is_shifted_uniform_family(c_family, n):
                    continue
                shifted_pairs.append((c_family, u_family, two_layer_boundary_size(c_family, u_family)))
        if not shifted_pairs:
            continue
        best_boundary = min(boundary_size for _, _, boundary_size in shifted_pairs)
        c_size = lower_count - e
        minimizer_pairs = [
            (c_family, u_family) for c_family, u_family, boundary_size in shifted_pairs
            if boundary_size == best_boundary
        ]
        equality_pairs = [
            (c_family, u_family) for c_family, u_family, boundary_size in shifted_pairs
            if boundary_size == c_size
        ]
        minimizer_reps = {canonical_orbit_rep(c_family, u_family) for c_family, u_family in minimizer_pairs}
        equality_reps = {canonical_orbit_rep(c_family, u_family) for c_family, u_family in equality_pairs}
        witness_c_family, witness_u_family = minimizer_pairs[0]
        if equality_pairs:
            witness_c_family, witness_u_family = equality_pairs[0]
        results.append(
            ExhaustiveShiftedTwoLayerExtremizerResult(
                n=n,
                e=e,
                minimal_boundary_size=best_boundary,
                minimal_margin=best_boundary - c_size,
                shifted_minimizer_count=len(minimizer_pairs),
                shifted_minimizer_orbit_count=len(minimizer_reps),
                equality_count=len(equality_pairs),
                equality_orbit_count=len(equality_reps),
                witness_c_family=witness_c_family,
                witness_u_family=witness_u_family,
            )
        )
    return results


def exhaustive_shifted_two_layer_summary(
    n: int,
) -> ExhaustiveShiftedTwoLayerSummaryResult:
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

    lower_shifted_families = enumerate_shifted_uniform_families(n, lower_rank, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, upper_rank, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], int] = {}

    def two_layer_boundary_size(c_family: Family, u_family: Family) -> int:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    worst_margin: int | None = None
    worst_margin_e = 0
    equality_count = 0
    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            for u_family in upper_by_size.get(e, []):
                margin = two_layer_boundary_size(c_family, u_family) - c_size
                if worst_margin is None or margin < worst_margin:
                    worst_margin = margin
                    worst_margin_e = e
                if margin == 0:
                    equality_count += 1

    return ExhaustiveShiftedTwoLayerSummaryResult(
        n=n,
        lower_shifted_family_count=len(lower_shifted_families),
        upper_shifted_family_count=len(upper_shifted_families),
        all_margins_nonnegative=(worst_margin is not None and worst_margin >= 0),
        worst_margin=0 if worst_margin is None else worst_margin,
        worst_margin_e=worst_margin_e,
        equality_count=equality_count,
    )


def shifted_two_layer_equality_orbits(
    n: int,
) -> List[ShiftedTwoLayerEqualityOrbitResult]:
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

    lower_shifted_families = enumerate_shifted_uniform_families(n, lower_rank, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, upper_rank, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], int] = {}

    def two_layer_boundary_size(c_family: Family, u_family: Family) -> int:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    perms = tuple(permutations(range(n)))

    def canonical_orbit_rep(c_family: Family, u_family: Family) -> Tuple[Family, Family]:
        candidates = [
            (permute_family(c_family, perm), permute_family(u_family, perm))
            for perm in perms
        ]
        return min(candidates)

    orbit_reps: Dict[Tuple[Family, Family], int] = {}
    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            for u_family in upper_by_size.get(e, []):
                if two_layer_boundary_size(c_family, u_family) != c_size:
                    continue
                orbit_reps.setdefault(canonical_orbit_rep(c_family, u_family), e)
    return [
        ShiftedTwoLayerEqualityOrbitResult(n=n, e=e, c_family=c_family, u_family=u_family)
        for (c_family, u_family), e in sorted(orbit_reps.items(), key=lambda item: (item[1], item[0]))
    ]


def exhaustive_shifted_even_adjacent_layer_summary(
    n: int,
) -> List[ExhaustiveShiftedEvenAdjacentLayerSummaryResult]:
    if n % 2 != 0:
        raise ValueError("n must be even")
    subsets = all_subsets(n)
    boundary_cache: Dict[Tuple[Family, Family], int] = {}

    def adjacent_layer_boundary_size(lower_family: Family, upper_family: Family) -> int:
        key = (lower_family, upper_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(lower_family + upper_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    results: List[ExhaustiveShiftedEvenAdjacentLayerSummaryResult] = []
    for r in range(n):
        lower_shifted_families = enumerate_shifted_uniform_families(n, r, subsets)
        upper_shifted_families = enumerate_shifted_uniform_families(n, r + 1, subsets)
        worst_margin: int | None = None
        equality_count = 0
        witness_lower_family: Family = ()
        witness_upper_family: Family = ()
        for lower_family in lower_shifted_families:
            lower_size = len(lower_family)
            for upper_family in upper_shifted_families:
                margin = adjacent_layer_boundary_size(lower_family, upper_family) - lower_size
                if worst_margin is None or margin < worst_margin:
                    worst_margin = margin
                    witness_lower_family = lower_family
                    witness_upper_family = upper_family
                if margin == 0:
                    equality_count += 1
        results.append(
            ExhaustiveShiftedEvenAdjacentLayerSummaryResult(
                n=n,
                r=r,
                lower_shifted_family_count=len(lower_shifted_families),
                upper_shifted_family_count=len(upper_shifted_families),
                all_margins_nonnegative=(worst_margin is not None and worst_margin >= 0),
                worst_margin=0 if worst_margin is None else worst_margin,
                equality_count=equality_count,
                witness_lower_family=witness_lower_family,
                witness_upper_family=witness_upper_family,
            )
        )
    return results


def exhaustive_coupled_section_summary(
    n: int,
) -> ExhaustiveCoupledSectionSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    section_subsets = all_subsets(n - 1)
    middle = n // 2
    lower_rank_sets = rank_subsets(n, middle, subsets)
    upper_rank_sets = rank_subsets(n, middle + 1, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    boundary_cache: Dict[Tuple[Family, Family], int] = {}

    def section_boundary_size(lower_family: Family, upper_family: Family) -> int:
        key = (lower_family, upper_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(lower_family + upper_family))
        value = len(positive_boundary(family, section_subsets))
        boundary_cache[key] = value
        return value

    worst_margin: int | None = None
    worst_margin_e = 0
    equality_count = 0
    witness_u_family: Family = ()
    witness_v_family: Family = ()
    witness_a_family: Family = ()
    witness_b_family: Family = ()
    witness_d_family: Family = ()
    witness_e_family: Family = ()

    for e in range(lower_count + 1):
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            d_family, e_family = section_split_at_zero(u_family)
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                v_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if v_mask & (1 << index)
                )
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                a_family, b_family = section_split_at_zero(c_family)
                lhs = section_boundary_size(a_family, d_family) + section_boundary_size(
                    b_family, e_family
                )
                rhs = len(a_family) + len(b_family)
                margin = lhs - rhs
                if worst_margin is None or margin < worst_margin:
                    worst_margin = margin
                    worst_margin_e = e
                    witness_u_family = u_family
                    witness_v_family = v_family
                    witness_a_family = a_family
                    witness_b_family = b_family
                    witness_d_family = d_family
                    witness_e_family = e_family
                if margin == 0:
                    equality_count += 1

    return ExhaustiveCoupledSectionSummaryResult(
        n=n,
        all_margins_nonnegative=(worst_margin is not None and worst_margin >= 0),
        worst_margin=0 if worst_margin is None else worst_margin,
        worst_margin_e=worst_margin_e,
        equality_count=equality_count,
        witness_u_family=witness_u_family,
        witness_v_family=witness_v_family,
        witness_a_family=witness_a_family,
        witness_b_family=witness_b_family,
        witness_d_family=witness_d_family,
        witness_e_family=witness_e_family,
    )


def shifted_coupled_section_summary(
    n: int,
) -> ShiftedCoupledSectionSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    section_subsets = all_subsets(n - 1)
    middle = n // 2
    lower_rank_sets = rank_subsets(n, middle, subsets)
    upper_rank_sets = rank_subsets(n, middle + 1, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    lower_shifted_families = enumerate_shifted_uniform_families(n, middle, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, middle + 1, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], int] = {}

    def section_boundary_size(lower_family: Family, upper_family: Family) -> int:
        key = (lower_family, upper_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(lower_family + upper_family))
        value = len(positive_boundary(family, section_subsets))
        boundary_cache[key] = value
        return value

    worst_margin: int | None = None
    worst_margin_e = 0
    equality_count = 0
    witness_c_family: Family = ()
    witness_u_family: Family = ()
    witness_a_family: Family = ()
    witness_b_family: Family = ()
    witness_d_family: Family = ()
    witness_e_family: Family = ()

    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            a_family, b_family = section_split_at_zero(c_family)
            rhs = len(a_family) + len(b_family)
            for u_family in upper_by_size.get(e, []):
                d_family, e_family = section_split_at_zero(u_family)
                lhs = section_boundary_size(a_family, d_family) + section_boundary_size(
                    b_family, e_family
                )
                margin = lhs - rhs
                if worst_margin is None or margin < worst_margin:
                    worst_margin = margin
                    worst_margin_e = e
                    witness_c_family = c_family
                    witness_u_family = u_family
                    witness_a_family = a_family
                    witness_b_family = b_family
                    witness_d_family = d_family
                    witness_e_family = e_family
                if margin == 0:
                    equality_count += 1

    return ShiftedCoupledSectionSummaryResult(
        n=n,
        lower_shifted_family_count=len(lower_shifted_families),
        upper_shifted_family_count=len(upper_shifted_families),
        all_margins_nonnegative=(worst_margin is not None and worst_margin >= 0),
        worst_margin=0 if worst_margin is None else worst_margin,
        worst_margin_e=worst_margin_e,
        equality_count=equality_count,
        witness_c_family=witness_c_family,
        witness_u_family=witness_u_family,
        witness_a_family=witness_a_family,
        witness_b_family=witness_b_family,
        witness_d_family=witness_d_family,
        witness_e_family=witness_e_family,
    )


def exhaustive_two_layer_local_flux_counterexample(
    n: int,
    max_codim: int,
) -> TwoLayerLocalFluxCounterexample | None:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    if max_codim <= 0:
        raise ValueError("max_codim must be positive")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank_sets = rank_subsets(n, middle, subsets)
    upper_rank_sets = rank_subsets(n, middle + 1, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    for e in range(lower_count + 1):
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                boundary = boundary_family(c_family, u_family)
                boundary_index = {member: index for index, member in enumerate(boundary)}
                neighbor_masks: List[int] = []
                for left in c_family:
                    neighborhood_mask = 0
                    for right in boundary:
                        if left & right == left:
                            codim = subset_cardinality(right) - subset_cardinality(left)
                            if 1 <= codim <= max_codim:
                                neighborhood_mask |= 1 << boundary_index[right]
                    neighbor_masks.append(neighborhood_mask)
                left_count = len(c_family)
                for left_subset_mask in range(1, 1 << left_count):
                    neighborhood_mask = 0
                    left_subset: List[int] = []
                    for index, neighborhood in enumerate(neighbor_masks):
                        if left_subset_mask & (1 << index):
                            neighborhood_mask |= neighborhood
                            left_subset.append(c_family[index])
                    if neighborhood_mask.bit_count() < len(left_subset):
                        violating_neighbor_family = tuple(
                            boundary[index]
                            for index in range(len(boundary))
                            if neighborhood_mask & (1 << index)
                        )
                        v_family = tuple(
                            lower_rank_sets[index]
                            for index in range(lower_count)
                            if v_mask & (1 << index)
                        )
                        return TwoLayerLocalFluxCounterexample(
                            n=n,
                            e=e,
                            max_codim=max_codim,
                            violating_left_family=tuple(left_subset),
                            violating_neighbor_family=violating_neighbor_family,
                            c_family=c_family,
                            u_family=u_family,
                            boundary_family=boundary,
                        )
    return None


def local_flux_adjacency(
    c_family: Sequence[int],
    boundary: Sequence[int],
    max_codim: int,
) -> List[Tuple[int, ...]]:
    boundary_index = {member: index for index, member in enumerate(boundary)}
    adjacency: List[Tuple[int, ...]] = []
    for left in c_family:
        neighbors: List[int] = []
        for right in boundary:
            if left & right == left:
                codim = subset_cardinality(right) - subset_cardinality(left)
                if 1 <= codim <= max_codim:
                    neighbors.append(boundary_index[right])
        adjacency.append(tuple(neighbors))
    return adjacency


def maximum_matching_size(adjacency: Sequence[Tuple[int, ...]], right_size: int) -> int:
    match_to_left = [-1] * right_size

    def augment(left: int, seen: List[bool]) -> bool:
        for right in adjacency[left]:
            if seen[right]:
                continue
            seen[right] = True
            current = match_to_left[right]
            if current == -1 or augment(current, seen):
                match_to_left[right] = left
                return True
        return False

    matched = 0
    for left in range(len(adjacency)):
        seen = [False] * right_size
        if augment(left, seen):
            matched += 1
    return matched


def shifted_two_layer_local_flux_summary(
    n: int,
    max_codim: int,
) -> ShiftedTwoLayerLocalFluxSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    if max_codim <= 0:
        raise ValueError("max_codim must be positive")
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

    lower_shifted_families = enumerate_shifted_uniform_families(n, lower_rank, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, upper_rank, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_deficiency: int | None = None
    worst_deficiency_e = 0
    witness_c_family: Family = ()
    witness_u_family: Family = ()
    witness_boundary_family: Family = ()

    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            for u_family in upper_by_size.get(e, []):
                boundary = boundary_family(c_family, u_family)
                adjacency = local_flux_adjacency(c_family, boundary, max_codim)
                matching_size = maximum_matching_size(adjacency, len(boundary))
                deficiency = matching_size - len(c_family)
                if worst_deficiency is None or deficiency < worst_deficiency:
                    worst_deficiency = deficiency
                    worst_deficiency_e = e
                    witness_c_family = c_family
                    witness_u_family = u_family
                    witness_boundary_family = boundary

    return ShiftedTwoLayerLocalFluxSummaryResult(
        n=n,
        max_codim=max_codim,
        lower_shifted_family_count=len(lower_shifted_families),
        upper_shifted_family_count=len(upper_shifted_families),
        all_pairs_have_matching=(worst_deficiency is not None and worst_deficiency >= 0),
        worst_deficiency=0 if worst_deficiency is None else worst_deficiency,
        worst_deficiency_e=worst_deficiency_e,
        witness_c_family=witness_c_family,
        witness_u_family=witness_u_family,
        witness_boundary_family=witness_boundary_family,
    )


def equal_split_worst_overload(
    c_family: Sequence[int],
    boundary: Sequence[int],
    max_codim: int,
) -> Tuple[Fraction, int | None, Fraction]:
    adjacency = local_flux_adjacency(c_family, boundary, max_codim)
    loads = [Fraction(0, 1) for _ in boundary]
    for neighbors in adjacency:
        if not neighbors:
            return (Fraction(1, 1), None, Fraction(0, 1))
        share = Fraction(1, len(neighbors))
        for right in neighbors:
            loads[right] += share
    if not loads:
        return (Fraction(-1, 1), None, Fraction(0, 1))
    worst_index = max(range(len(loads)), key=lambda idx: loads[idx])
    return (loads[worst_index] - 1, worst_index, loads[worst_index])


def inverse_degree_worst_overload(
    c_family: Sequence[int],
    boundary: Sequence[int],
    max_codim: int,
) -> Tuple[Fraction, int | None, Fraction]:
    adjacency = local_flux_adjacency(c_family, boundary, max_codim)
    right_degree = [0] * len(boundary)
    for neighbors in adjacency:
        for right in neighbors:
            right_degree[right] += 1
    loads = [Fraction(0, 1) for _ in boundary]
    for neighbors in adjacency:
        if not neighbors:
            return (Fraction(1, 1), None, Fraction(0, 1))
        weights = [Fraction(1, right_degree[right]) for right in neighbors]
        total = sum(weights, start=Fraction(0, 1))
        for right, raw_weight in zip(neighbors, weights):
            loads[right] += raw_weight / total
    if not loads:
        return (Fraction(-1, 1), None, Fraction(0, 1))
    worst_index = max(range(len(loads)), key=lambda idx: loads[idx])
    return (loads[worst_index] - 1, worst_index, loads[worst_index])


GREEDY_LOCAL_FLUX_RULE_SPECS: Tuple[Tuple[str, bool, bool, bool], ...] = (
    ("left-asc-codim-asc-boundary-asc", False, False, False),
    ("left-asc-codim-desc-boundary-asc", False, True, False),
    ("left-desc-codim-asc-boundary-asc", True, False, False),
    ("left-desc-codim-desc-boundary-asc", True, True, False),
    ("left-asc-codim-asc-boundary-desc", False, False, True),
    ("left-asc-codim-desc-boundary-desc", False, True, True),
    ("left-desc-codim-asc-boundary-desc", True, False, True),
    ("left-desc-codim-desc-boundary-desc", True, True, True),
)


def greedy_local_flux_match_deficiency(
    c_family: Sequence[int],
    boundary: Sequence[int],
    max_codim: int,
    left_desc: bool,
    codim_desc: bool,
    boundary_desc: bool,
) -> Tuple[int, Family]:
    adjacency = local_flux_adjacency(c_family, boundary, max_codim)
    left_order = sorted(range(len(c_family)), key=lambda idx: c_family[idx], reverse=left_desc)
    used_right: Set[int] = set()
    unmatched_left: List[int] = []
    matched = 0
    for left_index in left_order:
        neighbors = list(adjacency[left_index])
        neighbors.sort(
            key=lambda right_index: (
                -(
                    subset_cardinality(boundary[right_index])
                    - subset_cardinality(c_family[left_index])
                )
                if codim_desc
                else (
                    subset_cardinality(boundary[right_index])
                    - subset_cardinality(c_family[left_index])
                ),
                -boundary[right_index] if boundary_desc else boundary[right_index],
            )
        )
        chosen_right: int | None = None
        for right_index in neighbors:
            if right_index not in used_right:
                chosen_right = right_index
                break
        if chosen_right is None:
            unmatched_left.append(c_family[left_index])
            continue
        used_right.add(chosen_right)
        matched += 1
    return (matched - len(c_family), tuple(unmatched_left))


def exhaustive_two_layer_greedy_local_flux_summaries(
    n: int,
    max_codim: int,
) -> List[LocalFluxGreedySummaryResult]:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank_sets = rank_subsets(n, middle, subsets)
    upper_rank_sets = rank_subsets(n, middle + 1, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_by_rule: Dict[str, Tuple[int | None, int, Family, Family, Family, Family]] = {
        rule_name: (None, 0, (), (), (), ())
        for rule_name, _, _, _ in GREEDY_LOCAL_FLUX_RULE_SPECS
    }

    for e in range(lower_count + 1):
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                boundary = boundary_family(c_family, u_family)
                for rule_name, left_desc, codim_desc, boundary_desc in GREEDY_LOCAL_FLUX_RULE_SPECS:
                    deficiency, unmatched_left = greedy_local_flux_match_deficiency(
                        c_family, boundary, max_codim, left_desc, codim_desc, boundary_desc
                    )
                    worst_deficiency, _, _, _, _, _ = worst_by_rule[rule_name]
                    if worst_deficiency is None or deficiency < worst_deficiency:
                        worst_by_rule[rule_name] = (
                            deficiency,
                            e,
                            c_family,
                            u_family,
                            boundary,
                            unmatched_left,
                        )

    results: List[LocalFluxGreedySummaryResult] = []
    for rule_name, _, _, _ in GREEDY_LOCAL_FLUX_RULE_SPECS:
        worst_deficiency, worst_e, witness_c, witness_u, witness_boundary, unmatched_left = (
            worst_by_rule[rule_name]
        )
        results.append(
            LocalFluxGreedySummaryResult(
                rule_name=rule_name,
                n=n,
                max_codim=max_codim,
                exact_mode=True,
                all_pairs_have_matching=(worst_deficiency is not None and worst_deficiency >= 0),
                worst_deficiency=0 if worst_deficiency is None else worst_deficiency,
                worst_deficiency_e=worst_e,
                witness_c_family=witness_c,
                witness_u_family=witness_u,
                witness_boundary_family=witness_boundary,
                unmatched_left_family=unmatched_left,
            )
        )
    return results


def shifted_two_layer_greedy_local_flux_summaries(
    n: int,
    max_codim: int,
) -> List[LocalFluxGreedySummaryResult]:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank = middle
    upper_rank = middle + 1
    lower_count = comb(n, lower_rank)
    upper_count = comb(n, upper_rank)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    lower_shifted_families = enumerate_shifted_uniform_families(n, lower_rank, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, upper_rank, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_by_rule: Dict[str, Tuple[int | None, int, Family, Family, Family, Family]] = {
        rule_name: (None, 0, (), (), (), ())
        for rule_name, _, _, _ in GREEDY_LOCAL_FLUX_RULE_SPECS
    }

    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            for u_family in upper_by_size.get(e, []):
                boundary = boundary_family(c_family, u_family)
                for rule_name, left_desc, codim_desc, boundary_desc in GREEDY_LOCAL_FLUX_RULE_SPECS:
                    deficiency, unmatched_left = greedy_local_flux_match_deficiency(
                        c_family, boundary, max_codim, left_desc, codim_desc, boundary_desc
                    )
                    worst_deficiency, _, _, _, _, _ = worst_by_rule[rule_name]
                    if worst_deficiency is None or deficiency < worst_deficiency:
                        worst_by_rule[rule_name] = (
                            deficiency,
                            e,
                            c_family,
                            u_family,
                            boundary,
                            unmatched_left,
                        )

    results: List[LocalFluxGreedySummaryResult] = []
    for rule_name, _, _, _ in GREEDY_LOCAL_FLUX_RULE_SPECS:
        worst_deficiency, worst_e, witness_c, witness_u, witness_boundary, unmatched_left = (
            worst_by_rule[rule_name]
        )
        results.append(
            LocalFluxGreedySummaryResult(
                rule_name=rule_name,
                n=n,
                max_codim=max_codim,
                exact_mode=False,
                all_pairs_have_matching=(worst_deficiency is not None and worst_deficiency >= 0),
                worst_deficiency=0 if worst_deficiency is None else worst_deficiency,
                worst_deficiency_e=worst_e,
                witness_c_family=witness_c,
                witness_u_family=witness_u,
                witness_boundary_family=witness_boundary,
                unmatched_left_family=unmatched_left,
            )
        )
    return results


def exhaustive_two_layer_equal_split_summary(
    n: int,
    max_codim: int,
) -> LocalFluxEqualSplitSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank_sets = rank_subsets(n, middle, subsets)
    upper_rank_sets = rank_subsets(n, middle + 1, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_overload: Fraction | None = None
    worst_overload_e = 0
    witness_c_family: Family = ()
    witness_u_family: Family = ()
    witness_boundary_family: Family = ()
    witness_boundary_point: int | None = None
    witness_boundary_load = Fraction(0, 1)

    for e in range(lower_count + 1):
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                boundary = boundary_family(c_family, u_family)
                overload, point_index, point_load = equal_split_worst_overload(
                    c_family, boundary, max_codim
                )
                if worst_overload is None or overload > worst_overload:
                    worst_overload = overload
                    worst_overload_e = e
                    witness_c_family = c_family
                    witness_u_family = u_family
                    witness_boundary_family = boundary
                    witness_boundary_point = None if point_index is None else boundary[point_index]
                    witness_boundary_load = point_load

    return LocalFluxEqualSplitSummaryResult(
        n=n,
        max_codim=max_codim,
        exact_mode=True,
        all_pairs_respect_capacity=(worst_overload is not None and worst_overload <= 0),
        worst_overload=Fraction(0, 1) if worst_overload is None else worst_overload,
        worst_overload_e=worst_overload_e,
        witness_c_family=witness_c_family,
        witness_u_family=witness_u_family,
        witness_boundary_family=witness_boundary_family,
        witness_boundary_point=witness_boundary_point,
        witness_boundary_load=witness_boundary_load,
    )


def exhaustive_two_layer_inverse_degree_summary(
    n: int,
    max_codim: int,
) -> LocalFluxInverseDegreeSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank_sets = rank_subsets(n, middle, subsets)
    upper_rank_sets = rank_subsets(n, middle + 1, subsets)
    lower_count = len(lower_rank_sets)
    upper_count = len(upper_rank_sets)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_overload: Fraction | None = None
    worst_overload_e = 0
    witness_c_family: Family = ()
    witness_u_family: Family = ()
    witness_boundary_family: Family = ()
    witness_boundary_point: int | None = None
    witness_boundary_load = Fraction(0, 1)

    for e in range(lower_count + 1):
        for u_mask in range(1 << upper_count):
            if u_mask.bit_count() != e:
                continue
            u_family = tuple(
                upper_rank_sets[index] for index in range(upper_count) if u_mask & (1 << index)
            )
            for v_mask in range(1 << lower_count):
                if v_mask.bit_count() != e:
                    continue
                c_family = tuple(
                    lower_rank_sets[index]
                    for index in range(lower_count)
                    if not (v_mask & (1 << index))
                )
                boundary = boundary_family(c_family, u_family)
                overload, point_index, point_load = inverse_degree_worst_overload(
                    c_family, boundary, max_codim
                )
                if worst_overload is None or overload > worst_overload:
                    worst_overload = overload
                    worst_overload_e = e
                    witness_c_family = c_family
                    witness_u_family = u_family
                    witness_boundary_family = boundary
                    witness_boundary_point = None if point_index is None else boundary[point_index]
                    witness_boundary_load = point_load

    return LocalFluxInverseDegreeSummaryResult(
        n=n,
        max_codim=max_codim,
        exact_mode=True,
        all_pairs_respect_capacity=(worst_overload is not None and worst_overload <= 0),
        worst_overload=Fraction(0, 1) if worst_overload is None else worst_overload,
        worst_overload_e=worst_overload_e,
        witness_c_family=witness_c_family,
        witness_u_family=witness_u_family,
        witness_boundary_family=witness_boundary_family,
        witness_boundary_point=witness_boundary_point,
        witness_boundary_load=witness_boundary_load,
    )


def shifted_two_layer_equal_split_summary(
    n: int,
    max_codim: int,
) -> LocalFluxEqualSplitSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank = middle
    upper_rank = middle + 1
    lower_count = comb(n, lower_rank)
    upper_count = comb(n, upper_rank)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    lower_shifted_families = enumerate_shifted_uniform_families(n, lower_rank, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, upper_rank, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_overload: Fraction | None = None
    worst_overload_e = 0
    witness_c_family: Family = ()
    witness_u_family: Family = ()
    witness_boundary_family: Family = ()
    witness_boundary_point: int | None = None
    witness_boundary_load = Fraction(0, 1)

    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            for u_family in upper_by_size.get(e, []):
                boundary = boundary_family(c_family, u_family)
                overload, point_index, point_load = equal_split_worst_overload(
                    c_family, boundary, max_codim
                )
                if worst_overload is None or overload > worst_overload:
                    worst_overload = overload
                    worst_overload_e = e
                    witness_c_family = c_family
                    witness_u_family = u_family
                    witness_boundary_family = boundary
                    witness_boundary_point = None if point_index is None else boundary[point_index]
                    witness_boundary_load = point_load

    return LocalFluxEqualSplitSummaryResult(
        n=n,
        max_codim=max_codim,
        exact_mode=False,
        all_pairs_respect_capacity=(worst_overload is not None and worst_overload <= 0),
        worst_overload=Fraction(0, 1) if worst_overload is None else worst_overload,
        worst_overload_e=worst_overload_e,
        witness_c_family=witness_c_family,
        witness_u_family=witness_u_family,
        witness_boundary_family=witness_boundary_family,
        witness_boundary_point=witness_boundary_point,
        witness_boundary_load=witness_boundary_load,
    )


def shifted_two_layer_inverse_degree_summary(
    n: int,
    max_codim: int,
) -> LocalFluxInverseDegreeSummaryResult:
    if n % 2 == 0:
        raise ValueError("n must be odd")
    subsets = all_subsets(n)
    middle = n // 2
    lower_rank = middle
    upper_rank = middle + 1
    lower_count = comb(n, lower_rank)
    upper_count = comb(n, upper_rank)
    if lower_count != upper_count:
        raise ValueError("balanced middle layers must have equal size")

    lower_shifted_families = enumerate_shifted_uniform_families(n, lower_rank, subsets)
    upper_shifted_families = enumerate_shifted_uniform_families(n, upper_rank, subsets)
    lower_by_size: Dict[int, List[Family]] = {}
    upper_by_size: Dict[int, List[Family]] = {}
    for family in lower_shifted_families:
        lower_by_size.setdefault(len(family), []).append(family)
    for family in upper_shifted_families:
        upper_by_size.setdefault(len(family), []).append(family)

    boundary_cache: Dict[Tuple[Family, Family], Family] = {}

    def boundary_family(c_family: Family, u_family: Family) -> Family:
        key = (c_family, u_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(c_family + u_family))
        value = tuple(sorted(positive_boundary(family, subsets)))
        boundary_cache[key] = value
        return value

    worst_overload: Fraction | None = None
    worst_overload_e = 0
    witness_c_family: Family = ()
    witness_u_family: Family = ()
    witness_boundary_family: Family = ()
    witness_boundary_point: int | None = None
    witness_boundary_load = Fraction(0, 1)

    for e in range(lower_count + 1):
        c_size = lower_count - e
        for c_family in lower_by_size.get(c_size, []):
            for u_family in upper_by_size.get(e, []):
                boundary = boundary_family(c_family, u_family)
                overload, point_index, point_load = inverse_degree_worst_overload(
                    c_family, boundary, max_codim
                )
                if worst_overload is None or overload > worst_overload:
                    worst_overload = overload
                    worst_overload_e = e
                    witness_c_family = c_family
                    witness_u_family = u_family
                    witness_boundary_family = boundary
                    witness_boundary_point = None if point_index is None else boundary[point_index]
                    witness_boundary_load = point_load

    return LocalFluxInverseDegreeSummaryResult(
        n=n,
        max_codim=max_codim,
        exact_mode=False,
        all_pairs_respect_capacity=(worst_overload is not None and worst_overload <= 0),
        worst_overload=Fraction(0, 1) if worst_overload is None else worst_overload,
        worst_overload_e=worst_overload_e,
        witness_c_family=witness_c_family,
        witness_u_family=witness_u_family,
        witness_boundary_family=witness_boundary_family,
        witness_boundary_point=witness_boundary_point,
        witness_boundary_load=witness_boundary_load,
    )


def shifted_even_adjacent_layer_equality_orbits(
    n: int,
) -> List[ShiftedEvenAdjacentLayerEqualityOrbitResult]:
    if n % 2 != 0:
        raise ValueError("n must be even")
    subsets = all_subsets(n)
    perms = tuple(permutations(range(n)))
    boundary_cache: Dict[Tuple[Family, Family], int] = {}

    def adjacent_layer_boundary_size(lower_family: Family, upper_family: Family) -> int:
        key = (lower_family, upper_family)
        cached = boundary_cache.get(key)
        if cached is not None:
            return cached
        family = tuple(sorted(lower_family + upper_family))
        value = len(positive_boundary(family, subsets))
        boundary_cache[key] = value
        return value

    def canonical_orbit_rep(lower_family: Family, upper_family: Family) -> Tuple[Family, Family]:
        candidates = [
            (permute_family(lower_family, perm), permute_family(upper_family, perm))
            for perm in perms
        ]
        return min(candidates)

    orbit_reps: Dict[Tuple[int, Tuple[Family, Family]], None] = {}
    for r in range(n):
        lower_shifted_families = enumerate_shifted_uniform_families(n, r, subsets)
        upper_shifted_families = enumerate_shifted_uniform_families(n, r + 1, subsets)
        for lower_family in lower_shifted_families:
            lower_size = len(lower_family)
            for upper_family in upper_shifted_families:
                if adjacent_layer_boundary_size(lower_family, upper_family) != lower_size:
                    continue
                orbit_reps[(r, canonical_orbit_rep(lower_family, upper_family))] = None
    return [
        ShiftedEvenAdjacentLayerEqualityOrbitResult(
            n=n,
            r=r,
            lower_family=lower_family,
            upper_family=upper_family,
        )
        for (r, (lower_family, upper_family)) in sorted(orbit_reps.keys(), key=lambda item: (item[0], item[1]))
    ]


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
        "--exhaustive-two-layer-middle-boundary-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the direct two-layer boundary inequality "
            "|∂^+((([n] choose m) \\\\ V) ∪ U)| >= |([n] choose m) \\\\ V| over all equal-size "
            "middle-layer pairs."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-hall-shadow-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the stronger Hall-shadow sufficient criterion "
            "|∂^up U| >= |U \\\\ T(V)| over all equal-size middle-layer pairs."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-compression-route-n5",
        action="store_true",
        help=(
            "Run the exact n=5 diagnostics for the new compression-based direct route: "
            "check whether the lex/shifted model attains the minimum two-layer boundary and whether "
            "some boundary minimizer has shifted lower and upper slices."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-minimizer-orbits-n5",
        action="store_true",
        help=(
            "Run the exact n=5 orbit classification of all two-layer boundary minimizers: "
            "check whether every minimizer lies in the lex/shifted orbit."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-compression-monotonicity-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the actual two-layer compression lemma: "
            "check whether every layer-preserving shift weakly decreases |∂^+ F| "
            "for equal-size middle-layer pairs F = ((([n] choose m) \\\\ V) ∪ U)."
        ),
    )
    parser.add_argument(
        "--exhaustive-shifted-two-layer-extremizers-n5",
        action="store_true",
        help=(
            "Classify the exact n=5 shifted two-layer extremizers: for each e, report the "
            "minimal shifted boundary margin, the number of shifted minimizer orbits, "
            "and the shifted equality-orbit count."
        ),
    )
    parser.add_argument(
        "--shifted-uniform-family-counts",
        type=int,
        nargs="+",
        help=(
            "Count shifted uniform families on the given odd dimensions. "
            "For each odd n, report the number of shifted families in the middle ranks m and m+1."
        ),
    )
    parser.add_argument(
        "--exhaustive-shifted-two-layer-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only two-layer boundary summary on the given odd dimensions. "
            "For each odd n, enumerate all shifted middle-layer families, then report the "
            "worst shifted margin and equality count for |∂^+ F| >= |F ∩ ([n] choose m)|."
        ),
    )
    parser.add_argument(
        "--shifted-two-layer-equality-orbits",
        type=int,
        nargs="+",
        help=(
            "List the equality orbits in the shifted two-layer problem on the given odd dimensions. "
            "For each odd n, enumerate all shifted equality pairs up to permutation."
        ),
    )
    parser.add_argument(
        "--exhaustive-shifted-even-adjacent-layer-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only adjacent-layer boundary summary on the given even dimensions. "
            "For each even n and each rank r, enumerate shifted families in ranks r and r+1, then "
            "report the worst shifted margin for |∂^+ G| >= |G_r|."
        ),
    )
    parser.add_argument(
        "--shifted-even-adjacent-layer-equality-orbits",
        type=int,
        nargs="+",
        help=(
            "List the equality orbits in the shifted even adjacent-layer problem on the given even "
            "dimensions. For each even n, enumerate shifted equality pairs up to permutation."
        ),
    )
    parser.add_argument(
        "--exhaustive-coupled-section-summary-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the corrected coupled section inequality "
            "|∂^+(A ∪ D)| + |∂^+(B ∪ E)| >= |A| + |B| over all equal-size middle-layer pairs."
        ),
    )
    parser.add_argument(
        "--shifted-coupled-section-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only summary for the corrected coupled section inequality on the "
            "given odd dimensions."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-local-flux-n5",
        type=int,
        default=None,
        help=(
            "Run the exact n=5 Hall test for the naive local flux graph using predecessors of "
            "codimension at most the given value."
        ),
    )
    parser.add_argument(
        "--shifted-two-layer-local-flux-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only summary for the local flux Hall graph on the given odd "
            "dimensions."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-equal-split-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the equal-split codimension-bounded local flux rule, "
            "using --local-flux-max-codim to choose the transport graph."
        ),
    )
    parser.add_argument(
        "--shifted-two-layer-equal-split-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only summary for the equal-split codimension-bounded local flux rule "
            "on the given odd dimensions."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-inverse-degree-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of the inverse-degree codimension-bounded local flux rule, "
            "using --local-flux-max-codim to choose the transport graph."
        ),
    )
    parser.add_argument(
        "--shifted-two-layer-inverse-degree-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only summary for the inverse-degree codimension-bounded local flux "
            "rule on the given odd dimensions."
        ),
    )
    parser.add_argument(
        "--exhaustive-two-layer-greedy-local-match-n5",
        action="store_true",
        help=(
            "Run the exact n=5 test of several canonical greedy codimension-bounded local "
            "matching rules, using --local-flux-max-codim to choose the transport graph."
        ),
    )
    parser.add_argument(
        "--shifted-two-layer-greedy-local-match-summary",
        type=int,
        nargs="+",
        help=(
            "Run the shifted-only summary for several canonical greedy codimension-bounded local "
            "matching rules on the given odd dimensions."
        ),
    )
    parser.add_argument(
        "--local-flux-max-codim",
        type=int,
        default=2,
        help="Maximum predecessor codimension used by the local flux graph diagnostics.",
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

    if args.exhaustive_two_layer_middle_boundary_n5:
        any_warning = False
        results = exhaustive_two_layer_middle_boundary_minima(5)
        for result in results:
            if result.margin < 0:
                any_warning = True
                warn(
                    "WARNING exact n=5 two-layer boundary failure at "
                    f"e={result.e}: boundary={result.boundary_size} < |C|={result.c_size}"
                )
            else:
                ok(
                    "OK exact n=5 two-layer boundary at "
                    f"e={result.e}: boundary={result.boundary_size} >= |C|={result.c_size}"
                )
            print(
                f"  margin={result.margin} |C|={result.c_size} "
                f"U={format_family(result.witness_u_family)} "
                f"V={format_family(result.witness_v_family)}"
            )
        tightest = min(results, key=lambda result: (result.margin, result.e))
        print(
            "TIGHTEST exact n=5 class: "
            f"e={tightest.e} boundary={tightest.boundary_size} |C|={tightest.c_size} "
            f"margin={tightest.margin}"
        )
        if any_warning:
            warn("WARNING overall: the exact n=5 two-layer boundary inequality fails.")
            return 1
        ok("OK overall: the exact n=5 two-layer boundary inequality survives exhaustive search.")
        return 0

    if args.exhaustive_two_layer_hall_shadow_n5:
        any_warning = False
        results = exhaustive_two_layer_hall_shadow_minima(5)
        for result in results:
            if result.margin < 0:
                any_warning = True
                warn(
                    "WARNING exact n=5 Hall-shadow criterion failure at "
                    f"e={result.e}: shadow={result.upper_shadow_size} < damaged={result.damaged_u_size}"
                )
            else:
                ok(
                    "OK exact n=5 Hall-shadow criterion at "
                    f"e={result.e}: shadow={result.upper_shadow_size} >= damaged={result.damaged_u_size}"
                )
            print(
                f"  margin={result.margin} shadow={result.upper_shadow_size} "
                f"damaged={result.damaged_u_size} "
                f"U={format_family(result.witness_u_family)} "
                f"V={format_family(result.witness_v_family)}"
            )
        tightest = min(results, key=lambda result: (result.margin, result.e))
        print(
            "TIGHTEST exact n=5 Hall-shadow class: "
            f"e={tightest.e} shadow={tightest.upper_shadow_size} damaged={tightest.damaged_u_size} "
            f"margin={tightest.margin}"
        )
        if any_warning:
            warn("WARNING overall: the exact n=5 Hall-shadow criterion fails.")
            return 1
        ok("OK overall: the exact n=5 Hall-shadow criterion survives exhaustive search.")
        return 0

    if args.exhaustive_two_layer_compression_route_n5:
        any_warning = False
        results = exhaustive_two_layer_shifted_route_diagnostics(5)
        for result in results:
            if result.lex_shifted_gap == 0:
                ok(
                    "OK exact n=5 shifted route at "
                    f"e={result.e}: lex/shifted boundary matches the minimum {result.minimal_boundary_size}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING exact n=5 shifted route at "
                    f"e={result.e}: lex/shifted boundary={result.lex_shifted_boundary_size} "
                    f"> minimum={result.minimal_boundary_size}"
                )
            print(
                f"lex_shifted_gap={result.lex_shifted_gap} "
                f"has_shifted_minimizer={result.has_shifted_minimizer}"
            )
            if result.has_shifted_minimizer and result.shifted_witness_u_family is not None:
                print(
                    f"  shifted minimizer C={format_family(result.shifted_witness_c_family or ())} "
                    f"U={format_family(result.shifted_witness_u_family)}"
                )
        if any_warning:
            warn(
                "WARNING overall: the exact n=5 data do not support the naive lex/shifted model "
                "for the direct compression route."
            )
            return 1
        ok(
            "OK overall: exact n=5 data support the shifted-minimizer picture for the direct route."
        )
        return 0

    if args.exhaustive_two_layer_minimizer_orbits_n5:
        any_warning = False
        results = exhaustive_two_layer_minimizer_orbit_diagnostics(5)
        for result in results:
            if result.all_minimizers_in_lex_orbit:
                ok(
                    "OK exact n=5 minimizer orbit at "
                    f"e={result.e}: all {result.minimizer_count} minimizers lie in one lex orbit"
                )
            else:
                any_warning = True
                warn(
                    "WARNING exact n=5 minimizer orbit at "
                    f"e={result.e}: {result.orbit_count} minimizer orbits occur"
                )
            print(
                f"  min_boundary={result.minimal_boundary_size} "
                f"minimizer_count={result.minimizer_count} orbit_count={result.orbit_count}"
            )
        if any_warning:
            warn(
                "WARNING overall: exact n=5 data do not support uniqueness of the lex/shifted orbit."
            )
            return 1
        ok(
            "OK overall: exact n=5 data support lex/shifted orbit uniqueness for the direct route."
        )
        return 0

    if args.exhaustive_two_layer_compression_monotonicity_n5:
        result = exhaustive_two_layer_boundary_compression_counterexample(5)
        if result is None:
            ok(
                "OK exact n=5: every layer-preserving two-layer shift weakly decreases |∂^+ F|."
            )
            return 0
        warn("WARNING exact n=5: the actual two-layer compression lemma fails.")
        print(
            f"  e={result.e} compression=(i,j)=({result.i},{result.j}) "
            f"boundary_before={result.boundary_before} boundary_after={result.boundary_after}"
        )
        print(f"  C = {format_family(result.c_family)}")
        print(f"  U = {format_family(result.u_family)}")
        print(f"  C' = {format_family(result.compressed_c_family)}")
        print(f"  U' = {format_family(result.compressed_u_family)}")
        return 1

    if args.exhaustive_shifted_two_layer_extremizers_n5:
        results = exhaustive_shifted_two_layer_extremizers(5)
        for result in results:
            if result.equality_count > 0:
                ok(
                    "OK exact n=5 shifted equality at "
                    f"e={result.e}: equality_orbits={result.equality_orbit_count}"
                )
            else:
                ok(
                    "OK exact n=5 shifted minimum at "
                    f"e={result.e}: min_margin={result.minimal_margin}"
                )
            print(
                f"  min_margin={result.minimal_margin} "
                f"shifted_minimizers={result.shifted_minimizer_count} "
                f"shifted_minimizer_orbits={result.shifted_minimizer_orbit_count} "
                f"equality_count={result.equality_count} "
                f"equality_orbits={result.equality_orbit_count}"
            )
            print(
                f"  witness C={format_family(result.witness_c_family)} "
                f"U={format_family(result.witness_u_family)}"
            )
        ok("OK overall: exact n=5 shifted two-layer extremizers classified.")
        return 0

    if args.shifted_uniform_family_counts is not None:
        for n in args.shifted_uniform_family_counts:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                return 1
            subsets = all_subsets(n)
            middle = n // 2
            lower_count = len(enumerate_shifted_uniform_families(n, middle, subsets))
            upper_count = len(enumerate_shifted_uniform_families(n, middle + 1, subsets))
            ok(
                f"OK shifted-family counts at n={n}: "
                f"rank-{middle}={lower_count}, rank-{middle + 1}={upper_count}"
            )
        return 0

    if args.exhaustive_shifted_two_layer_summary is not None:
        any_warning = False
        for n in args.exhaustive_shifted_two_layer_summary:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            result = exhaustive_shifted_two_layer_summary(n)
            if result.all_margins_nonnegative:
                ok(
                    "OK shifted two-layer summary at "
                    f"n={n}: worst_margin={result.worst_margin} at e={result.worst_margin_e}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING shifted two-layer failure at "
                    f"n={n}: worst_margin={result.worst_margin} at e={result.worst_margin_e}"
                )
            print(
                f"  lower_shifted_families={result.lower_shifted_family_count} "
                f"upper_shifted_families={result.upper_shifted_family_count} "
                f"equality_count={result.equality_count}"
            )
        if any_warning:
            warn("WARNING overall: some shifted two-layer summaries failed.")
            return 1
        ok("OK overall: all requested shifted two-layer summaries survived.")
        return 0

    if args.shifted_two_layer_equality_orbits is not None:
        for n in args.shifted_two_layer_equality_orbits:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                return 1
            results = shifted_two_layer_equality_orbits(n)
            ok(f"OK shifted two-layer equality orbits at n={n}: orbit_count={len(results)}")
            for result in results:
                print(f"  e={result.e} C={format_family(result.c_family)} U={format_family(result.u_family)}")
        return 0

    if args.exhaustive_shifted_even_adjacent_layer_summary is not None:
        any_warning = False
        for n in args.exhaustive_shifted_even_adjacent_layer_summary:
            if n % 2 != 0:
                warn(f"WARNING requested odd dimension n={n}; this mode expects even dimensions.")
                any_warning = True
                continue
            results = exhaustive_shifted_even_adjacent_layer_summary(n)
            for result in results:
                if result.all_margins_nonnegative:
                    ok(
                        "OK shifted even adjacent-layer summary at "
                        f"n={n}, r={result.r}: worst_margin={result.worst_margin}"
                    )
                else:
                    any_warning = True
                    warn(
                        "WARNING shifted even adjacent-layer failure at "
                        f"n={n}, r={result.r}: worst_margin={result.worst_margin}"
                    )
                print(
                    f"  lower_shifted_families={result.lower_shifted_family_count} "
                    f"upper_shifted_families={result.upper_shifted_family_count} "
                    f"equality_count={result.equality_count}"
                )
                print(
                    f"  witness lower={format_family(result.witness_lower_family)} "
                    f"upper={format_family(result.witness_upper_family)}"
                )
        if any_warning:
            warn("WARNING overall: some shifted even adjacent-layer summaries failed.")
            return 1
        ok("OK overall: all requested shifted even adjacent-layer summaries survived.")
        return 0

    if args.shifted_even_adjacent_layer_equality_orbits is not None:
        for n in args.shifted_even_adjacent_layer_equality_orbits:
            if n % 2 != 0:
                warn(f"WARNING requested odd dimension n={n}; this mode expects even dimensions.")
                return 1
            results = shifted_even_adjacent_layer_equality_orbits(n)
            ok(
                f"OK shifted even adjacent-layer equality orbits at n={n}: orbit_count={len(results)}"
            )
            for result in results:
                print(
                    f"  r={result.r} lower={format_family(result.lower_family)} "
                    f"upper={format_family(result.upper_family)}"
                )
        return 0

    if args.exhaustive_coupled_section_summary_n5:
        result = exhaustive_coupled_section_summary(5)
        if result.all_margins_nonnegative:
            ok(
                "OK exact n=5 coupled section summary: "
                f"worst_margin={result.worst_margin} at e={result.worst_margin_e}"
            )
        else:
            warn(
                "WARNING exact n=5 coupled section failure: "
                f"worst_margin={result.worst_margin} at e={result.worst_margin_e}"
            )
        print(f"  equality_count={result.equality_count}")
        print(f"  witness U={format_family(result.witness_u_family)}")
        print(f"  witness V={format_family(result.witness_v_family)}")
        print(
            "  sections "
            f"A={format_family(result.witness_a_family)} "
            f"B={format_family(result.witness_b_family)} "
            f"D={format_family(result.witness_d_family)} "
            f"E={format_family(result.witness_e_family)}"
        )
        return 0 if result.all_margins_nonnegative else 1

    if args.shifted_coupled_section_summary is not None:
        any_warning = False
        for n in args.shifted_coupled_section_summary:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            result = shifted_coupled_section_summary(n)
            if result.all_margins_nonnegative:
                ok(
                    "OK shifted coupled section summary at "
                    f"n={n}: worst_margin={result.worst_margin} at e={result.worst_margin_e}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING shifted coupled section failure at "
                    f"n={n}: worst_margin={result.worst_margin} at e={result.worst_margin_e}"
                )
            print(
                f"  lower_shifted_families={result.lower_shifted_family_count} "
                f"upper_shifted_families={result.upper_shifted_family_count} "
                f"equality_count={result.equality_count}"
            )
            print(
                f"  witness C={format_family(result.witness_c_family)} "
                f"U={format_family(result.witness_u_family)}"
            )
            print(
                "  sections "
                f"A={format_family(result.witness_a_family)} "
                f"B={format_family(result.witness_b_family)} "
                f"D={format_family(result.witness_d_family)} "
                f"E={format_family(result.witness_e_family)}"
            )
        if any_warning:
            warn("WARNING overall: some shifted coupled section summaries failed.")
            return 1
        ok("OK overall: all requested shifted coupled section summaries survived.")
        return 0

    if args.exhaustive_two_layer_local_flux_n5 is not None:
        result = exhaustive_two_layer_local_flux_counterexample(5, args.exhaustive_two_layer_local_flux_n5)
        if result is None:
            ok(
                "OK exact n=5: the naive local flux Hall condition survives "
                f"for max_codim={args.exhaustive_two_layer_local_flux_n5}."
            )
            return 0
        warn(
            "WARNING exact n=5: the naive local flux Hall condition fails "
            f"for max_codim={result.max_codim} at e={result.e}."
        )
        print(f"  violating left family={format_family(result.violating_left_family)}")
        print(f"  violating neighborhood={format_family(result.violating_neighbor_family)}")
        print(f"  C={format_family(result.c_family)}")
        print(f"  U={format_family(result.u_family)}")
        print(f"  boundary={format_family(result.boundary_family)}")
        return 1

    if args.shifted_two_layer_local_flux_summary is not None:
        any_warning = False
        for n in args.shifted_two_layer_local_flux_summary:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            result = shifted_two_layer_local_flux_summary(n, args.local_flux_max_codim)
            if result.all_pairs_have_matching:
                ok(
                    "OK shifted local flux summary at "
                    f"n={n}, max_codim={result.max_codim}: "
                    f"worst_deficiency={result.worst_deficiency} at e={result.worst_deficiency_e}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING shifted local flux failure at "
                    f"n={n}, max_codim={result.max_codim}: "
                    f"worst_deficiency={result.worst_deficiency} at e={result.worst_deficiency_e}"
                )
            print(
                f"  lower_shifted_families={result.lower_shifted_family_count} "
                f"upper_shifted_families={result.upper_shifted_family_count}"
            )
            print(
                f"  witness C={format_family(result.witness_c_family)} "
                f"U={format_family(result.witness_u_family)}"
            )
            print(f"  witness boundary={format_family(result.witness_boundary_family)}")
        if any_warning:
            warn("WARNING overall: some shifted local flux summaries failed.")
            return 1
        ok("OK overall: all requested shifted local flux summaries survived.")
        return 0

    if args.exhaustive_two_layer_equal_split_n5:
        result = exhaustive_two_layer_equal_split_summary(5, args.local_flux_max_codim)
        if result.all_pairs_respect_capacity:
            ok(
                "OK exact n=5 equal-split local flux at "
                f"max_codim={result.max_codim}: "
                f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
            )
            return 0
        warn(
            "WARNING exact n=5 equal-split local flux overload at "
            f"max_codim={result.max_codim}: "
            f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
        )
        print(f"  witness C={format_family(result.witness_c_family)}")
        print(f"  witness U={format_family(result.witness_u_family)}")
        print(f"  witness boundary={format_family(result.witness_boundary_family)}")
        if result.witness_boundary_point is not None:
            print(
                f"  overloaded boundary point={format_subset(result.witness_boundary_point)} "
                f"load={result.witness_boundary_load}"
            )
        return 1

    if args.shifted_two_layer_equal_split_summary is not None:
        any_warning = False
        for n in args.shifted_two_layer_equal_split_summary:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            result = shifted_two_layer_equal_split_summary(n, args.local_flux_max_codim)
            if result.all_pairs_respect_capacity:
                ok(
                    "OK shifted equal-split local flux at "
                    f"n={n}, max_codim={result.max_codim}: "
                    f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING shifted equal-split local flux overload at "
                    f"n={n}, max_codim={result.max_codim}: "
                    f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
                )
            print(
                f"  witness C={format_family(result.witness_c_family)} "
                f"U={format_family(result.witness_u_family)}"
            )
            print(f"  witness boundary={format_family(result.witness_boundary_family)}")
            if result.witness_boundary_point is not None:
                print(
                    f"  boundary point={format_subset(result.witness_boundary_point)} "
                    f"load={result.witness_boundary_load}"
                )
        if any_warning:
            warn("WARNING overall: some shifted equal-split local flux summaries failed.")
            return 1
        ok("OK overall: all requested shifted equal-split local flux summaries survived.")
        return 0

    if args.exhaustive_two_layer_inverse_degree_n5:
        result = exhaustive_two_layer_inverse_degree_summary(5, args.local_flux_max_codim)
        if result.all_pairs_respect_capacity:
            ok(
                "OK exact n=5 inverse-degree local flux at "
                f"max_codim={result.max_codim}: "
                f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
            )
            return 0
        warn(
            "WARNING exact n=5 inverse-degree local flux overload at "
            f"max_codim={result.max_codim}: "
            f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
        )
        print(f"  witness C={format_family(result.witness_c_family)}")
        print(f"  witness U={format_family(result.witness_u_family)}")
        print(f"  witness boundary={format_family(result.witness_boundary_family)}")
        if result.witness_boundary_point is not None:
            print(
                f"  overloaded boundary point={format_subset(result.witness_boundary_point)} "
                f"load={result.witness_boundary_load}"
            )
        return 1

    if args.shifted_two_layer_inverse_degree_summary is not None:
        any_warning = False
        for n in args.shifted_two_layer_inverse_degree_summary:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            result = shifted_two_layer_inverse_degree_summary(n, args.local_flux_max_codim)
            if result.all_pairs_respect_capacity:
                ok(
                    "OK shifted inverse-degree local flux at "
                    f"n={n}, max_codim={result.max_codim}: "
                    f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING shifted inverse-degree local flux overload at "
                    f"n={n}, max_codim={result.max_codim}: "
                    f"worst_overload={result.worst_overload} at e={result.worst_overload_e}"
                )
            print(
                f"  witness C={format_family(result.witness_c_family)} "
                f"U={format_family(result.witness_u_family)}"
            )
            print(f"  witness boundary={format_family(result.witness_boundary_family)}")
            if result.witness_boundary_point is not None:
                print(
                    f"  boundary point={format_subset(result.witness_boundary_point)} "
                    f"load={result.witness_boundary_load}"
                )
        if any_warning:
            warn("WARNING overall: some shifted inverse-degree local flux summaries failed.")
            return 1
        ok("OK overall: all requested shifted inverse-degree local flux summaries survived.")
        return 0

    if args.exhaustive_two_layer_greedy_local_match_n5:
        any_warning = False
        for result in exhaustive_two_layer_greedy_local_flux_summaries(
            5, args.local_flux_max_codim
        ):
            if result.all_pairs_have_matching:
                ok(
                    "OK exact n=5 greedy local matching "
                    f"rule={result.rule_name}, max_codim={result.max_codim}: "
                    f"worst_deficiency={result.worst_deficiency} at e={result.worst_deficiency_e}"
                )
            else:
                any_warning = True
                warn(
                    "WARNING exact n=5 greedy local matching "
                    f"rule={result.rule_name}, max_codim={result.max_codim}: "
                    f"worst_deficiency={result.worst_deficiency} at e={result.worst_deficiency_e}"
                )
                print(f"  witness C={format_family(result.witness_c_family)}")
                print(f"  witness U={format_family(result.witness_u_family)}")
                print(f"  witness boundary={format_family(result.witness_boundary_family)}")
                print(f"  unmatched={format_family(result.unmatched_left_family)}")
        if any_warning:
            warn("WARNING overall: some exact n=5 greedy local matching rules failed.")
            return 1
        ok("OK overall: all exact n=5 greedy local matching rules survived.")
        return 0

    if args.shifted_two_layer_greedy_local_match_summary is not None:
        any_warning = False
        for n in args.shifted_two_layer_greedy_local_match_summary:
            if n % 2 == 0:
                warn(f"WARNING requested even dimension n={n}; this mode expects odd dimensions.")
                any_warning = True
                continue
            for result in shifted_two_layer_greedy_local_flux_summaries(
                n, args.local_flux_max_codim
            ):
                if result.all_pairs_have_matching:
                    ok(
                        "OK shifted greedy local matching "
                        f"rule={result.rule_name}, n={n}, max_codim={result.max_codim}: "
                        f"worst_deficiency={result.worst_deficiency} at e={result.worst_deficiency_e}"
                    )
                else:
                    any_warning = True
                    warn(
                        "WARNING shifted greedy local matching "
                        f"rule={result.rule_name}, n={n}, max_codim={result.max_codim}: "
                        f"worst_deficiency={result.worst_deficiency} at e={result.worst_deficiency_e}"
                    )
                    print(
                        f"  witness C={format_family(result.witness_c_family)} "
                        f"U={format_family(result.witness_u_family)}"
                    )
                    print(f"  witness boundary={format_family(result.witness_boundary_family)}")
                    print(f"  unmatched={format_family(result.unmatched_left_family)}")
        if any_warning:
            warn("WARNING overall: some shifted greedy local matching rules failed.")
            return 1
        ok("OK overall: all requested shifted greedy local matching rules survived.")
        return 0

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
