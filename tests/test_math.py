import math
import pytest

from analyze_results import pass_at_k_unbiased, bootstrap_ci
from hivemind import compute_hivemind


class TestPassAtK:
    def test_zero_correct_returns_zero(self):
        assert pass_at_k_unbiased(n=10, c=0, k=1) == 0.0

    def test_all_correct_returns_one(self):
        assert pass_at_k_unbiased(n=10, c=10, k=1) == 1.0
        assert pass_at_k_unbiased(n=10, c=10, k=3) == 1.0

    def test_pass_at_1_equals_c_over_n(self):
        n, c = 20, 8
        assert abs(pass_at_k_unbiased(n, c, 1) - c / n) < 1e-9

    def test_pass_at_k_increases_with_c(self):
        n = 10
        assert pass_at_k_unbiased(n, c=2, k=3) < pass_at_k_unbiased(n, c=8, k=3)

    def test_pass_at_k_increases_with_k(self):
        n, c = 10, 5
        assert pass_at_k_unbiased(n, c, 1) <= pass_at_k_unbiased(n, c, 3)

    def test_k_greater_than_n_returns_zero(self):
        assert pass_at_k_unbiased(n=3, c=2, k=5) == 0.0

    def test_empty_set_returns_zero(self):
        assert pass_at_k_unbiased(n=0, c=0, k=1) == 0.0

    def test_known_value(self):
        # 1 - C(5,3)/C(10,3)
        expected = 1.0 - math.comb(5, 3) / math.comb(10, 3)
        assert abs(pass_at_k_unbiased(n=10, c=5, k=3) - expected) < 1e-9

    def test_n_minus_c_less_than_k_returns_one(self):
        assert pass_at_k_unbiased(n=5, c=4, k=3) == 1.0


class TestBootstrapCI:
    def test_returns_two_floats(self):
        lo, hi = bootstrap_ci([0, 1, 0, 1, 1])
        assert isinstance(lo, float) and isinstance(hi, float)

    def test_lo_le_hi(self):
        lo, hi = bootstrap_ci([0.2, 0.4, 0.6, 0.8])
        assert lo <= hi

    def test_empty_returns_zero_zero(self):
        assert bootstrap_ci([]) == (0.0, 0.0)

    def test_constant_input_tight_interval(self):
        lo, hi = bootstrap_ci([0.5] * 100)
        assert abs(lo - 0.5) < 0.01 and abs(hi - 0.5) < 0.01

    def test_interval_contains_true_mean(self):
        import numpy as np
        values = list(np.random.default_rng(0).binomial(1, 0.6, 200).astype(float))
        lo, hi = bootstrap_ci(values, n_boot=2000)
        assert lo <= 0.6 <= hi

    def test_more_spread_gives_wider_ci(self):
        lo_n, hi_n = bootstrap_ci([0.5] * 50)
        lo_w, hi_w = bootstrap_ci([0.0] * 25 + [1.0] * 25)
        assert (hi_w - lo_w) > (hi_n - lo_n)


class TestHivemindIndex:
    def test_perfect_agreement_h_is_one(self):
        failures = {"m1": {1, 2, 3}, "m2": {1, 2, 3}, "m3": {1, 2, 3}}
        assert compute_hivemind(failures, {1, 2, 3, 4, 5})["H"] == 1.0

    def test_no_overlap_h_is_zero(self):
        failures = {"m1": {1, 2}, "m2": {3, 4}}
        assert compute_hivemind(failures, {1, 2, 3, 4})["H"] == 0.0

    def test_known_jaccard(self):
        # intersection={2}, union={1,2,3} → H = 1/3
        failures = {"m1": {1, 2}, "m2": {2, 3}}
        assert abs(compute_hivemind(failures, {1, 2, 3, 4})["H"] - 1 / 3) < 1e-4

    def test_single_model_note(self):
        result = compute_hivemind({"m1": {1, 2}}, {1, 2, 3})
        assert "only one model" in result.get("note", "")

    def test_no_failures_returns_none(self):
        assert compute_hivemind({"m1": set(), "m2": set()}, {1, 2, 3})["H"] is None

    def test_h_in_unit_interval(self):
        failures = {"m1": {1, 2, 3}, "m2": {2, 3, 4}, "m3": {3, 4, 5}}
        h = compute_hivemind(failures, set(range(1, 11)))["H"]
        assert 0.0 <= h <= 1.0

    def test_intersection_and_union_sizes(self):
        result = compute_hivemind({"m1": {1, 2, 3}, "m2": {2, 3, 4}}, {1, 2, 3, 4, 5})
        assert result["n_intersection"] == 2
        assert result["n_union"] == 4

    def test_ratio_matches_h_over_h_ind(self):
        result = compute_hivemind({"m1": {1, 2, 3}, "m2": {2, 3, 4}}, {1, 2, 3, 4, 5})
        if result["H_ind"] and result["H_ind"] > 0:
            assert abs(result["ratio"] - round(result["H"] / result["H_ind"], 2)) < 0.01
