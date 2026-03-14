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
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Exhaustive low-dimensional search for the odd-cube boundary program in Problem #1."
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

    dimensions = tuple(args.dimensions)
    total_steps = len(dimensions) * 7
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
