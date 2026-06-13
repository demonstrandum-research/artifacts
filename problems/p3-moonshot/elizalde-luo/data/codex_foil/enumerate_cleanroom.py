from __future__ import annotations

from collections import Counter
from itertools import combinations
import json


PATTERNS = {
    "1221": (1, 2, 2, 1),
    "2112": (2, 1, 1, 2),
    "1132": (1, 1, 3, 2),
    "3312": (3, 3, 1, 2),
}


def relation(a: int, b: int) -> int:
    if a < b:
        return -1
    if a > b:
        return 1
    return 0


class LiteralPatternChecker:
    def __init__(self) -> None:
        self._cache: dict[tuple[int, tuple[int, ...]], tuple[list[tuple[int, ...]], list[tuple[int, int, int]]]] = {}

    def contains(self, word: tuple[int, ...], pattern: tuple[int, ...]) -> bool:
        """Literal subsequence containment: compare all pairwise order/equality relations."""
        key = (len(word), pattern)
        if key not in self._cache:
            k = len(pattern)
            pairs = [(r, s, relation(pattern[r], pattern[s])) for r in range(k) for s in range(r + 1, k)]
            self._cache[key] = (list(combinations(range(len(word)), k)), pairs)
        index_sets, pairs = self._cache[key]

        for indices in index_sets:
            ok = True
            for r, s, want in pairs:
                if relation(word[indices[r]], word[indices[s]]) != want:
                    ok = False
                    break
            if ok:
                return True
        return False


def multiset_permutations(n: int):
    counts = [0] + [2] * n
    word: list[int] = []
    target_len = 2 * n

    def rec():
        if len(word) == target_len:
            yield tuple(word)
            return
        for value in range(1, n + 1):
            if counts[value]:
                counts[value] -= 1
                word.append(value)
                yield from rec()
                word.pop()
                counts[value] += 1

    yield from rec()


def nonnesting_fifo_words(n: int):
    """Generate words whose second occurrences close the earliest still-open first occurrence."""
    unopened = [True] * (n + 1)
    open_queue: list[int] = []
    word: list[int] = []
    target_len = 2 * n

    def rec(opened_count: int):
        if len(word) == target_len:
            yield tuple(word)
            return

        if open_queue:
            value = open_queue.pop(0)
            word.append(value)
            yield from rec(opened_count)
            word.pop()
            open_queue.insert(0, value)

        if opened_count < n:
            for value in range(1, n + 1):
                if unopened[value]:
                    unopened[value] = False
                    open_queue.append(value)
                    word.append(value)
                    yield from rec(opened_count + 1)
                    word.pop()
                    open_queue.pop()
                    unopened[value] = True

    yield from rec(0)


def descent_count(word: tuple[int, ...]) -> int:
    return sum(1 for i in range(len(word) - 1) if word[i] > word[i + 1])


def positions_of_value(word: tuple[int, ...], value: int) -> str:
    positions = [i + 1 for i, item in enumerate(word) if item == value]
    return f"{positions[0]},{positions[1]}"


def main() -> None:
    checker = LiteralPatternChecker()
    nonnesting_totals: dict[str, int] = {}
    avoider_counts: dict[str, int] = {}
    literal_nonnesting_sets: dict[int, set[tuple[int, ...]]] = {}
    avoider_words: dict[int, list[tuple[int, ...]]] = {}

    for n in range(1, 6):
        nn_words: set[tuple[int, ...]] = set()
        av_words: list[tuple[int, ...]] = []
        for word in multiset_permutations(n):
            nonnesting = (
                not checker.contains(word, PATTERNS["1221"])
                and not checker.contains(word, PATTERNS["2112"])
            )
            if nonnesting:
                nn_words.add(word)
                if (
                    not checker.contains(word, PATTERNS["1132"])
                    and not checker.contains(word, PATTERNS["3312"])
                ):
                    av_words.append(word)

        literal_nonnesting_sets[n] = nn_words
        avoider_words[n] = av_words
        nonnesting_totals[str(n)] = len(nn_words)
        avoider_counts[str(n)] = len(av_words)

    for n in range(1, 6):
        generated = set(nonnesting_fifo_words(n))
        if generated != literal_nonnesting_sets[n]:
            missing = literal_nonnesting_sets[n] - generated
            extra = generated - literal_nonnesting_sets[n]
            raise AssertionError(
                f"FIFO validation failed for n={n}: missing={len(missing)} extra={len(extra)}"
            )

    n = 6
    total6 = 0
    avoid6 = 0
    for word in nonnesting_fifo_words(n):
        total6 += 1
        if (
            not checker.contains(word, PATTERNS["1132"])
            and not checker.contains(word, PATTERNS["3312"])
        ):
            avoid6 += 1
    nonnesting_totals[str(n)] = total6
    avoider_counts[str(n)] = avoid6

    descents_n4 = Counter(descent_count(word) for word in avoider_words[4])
    descents_n5 = Counter(descent_count(word) for word in avoider_words[5])
    first_letter_n5 = Counter(word[0] for word in avoider_words[5])
    positions_n5 = Counter(positions_of_value(word, 5) for word in avoider_words[5])

    result = {
        "nonnesting_totals": nonnesting_totals,
        "avoider_counts": avoider_counts,
        "descents_n4": {str(k): descents_n4[k] for k in sorted(descents_n4)},
        "descents_n5": {str(k): descents_n5[k] for k in sorted(descents_n5)},
        "first_letter_n5": {str(k): first_letter_n5[k] for k in sorted(first_letter_n5)},
        "positions_of_n_n5": {k: positions_n5[k] for k in sorted(positions_n5, key=lambda x: tuple(map(int, x.split(","))))},
        "method_notes": (
            "Literal subsequence containment with pairwise order/equality comparisons was run over every "
            "multiset permutation for n<=5. For n=6, nonnesting words were generated by the independently "
            "derived FIFO closure rule for nonnested arcs; this generator was exhaustively validated against "
            "the literal all-permutation path for n=1..5. Avoidance of 1132 and 3312 was still checked by "
            "the literal subsequence scan."
        ),
    }
    print(json.dumps(result, indent=2, sort_keys=False))


if __name__ == "__main__":
    main()
