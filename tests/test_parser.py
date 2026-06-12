import pytest
from parser import extract_tla_from_response

MINIMAL = "---- MODULE Foo ----\nVARIABLES x\nInit == x = 0\nNext == x' = x + 1\n===="


class TestFenceBlock:
    def test_tla_fence(self):
        assert "MODULE Foo" in extract_tla_from_response(f"```tla\n{MINIMAL}\n```")

    def test_tlaplus_fence(self):
        assert extract_tla_from_response(f"```tla+\n{MINIMAL}\n```") is not None

    def test_uppercase_fence(self):
        assert extract_tla_from_response(f"```TLA\n{MINIMAL}\n```") is not None

    def test_plain_fence_with_module(self):
        assert extract_tla_from_response(f"```\n{MINIMAL}\n```") is not None

    def test_prefers_fence_with_module_keyword(self):
        response = "```\nsome code\n```\n```tla\n" + MINIMAL + "\n```"
        result = extract_tla_from_response(response)
        assert result is not None and "MODULE" in result


class TestBareModule:
    def test_bare_module(self):
        assert "MODULE Foo" in extract_tla_from_response(f"The spec:\n{MINIMAL}\nDone.")

    def test_long_dashes(self):
        spec = "-------- MODULE Bar --------\nVARIABLES y\n===="
        assert extract_tla_from_response(spec) is not None


class TestThinkStripping:
    def test_think_block_removed(self):
        result = extract_tla_from_response(f"<think>reasoning</think>\n{MINIMAL}")
        assert result is not None and "<think>" not in result

    def test_think_with_fenced_spec(self):
        result = extract_tla_from_response(f"<think>x</think>\n```tla\n{MINIMAL}\n```")
        assert result is not None and "MODULE" in result

    def test_multiline_think(self):
        result = extract_tla_from_response(f"<think>\nstep 1\nstep 2\n</think>\n{MINIMAL}")
        assert result is not None


class TestFailure:
    def test_empty(self):
        assert extract_tla_from_response("") is None

    def test_no_module(self):
        assert extract_tla_from_response("just some text") is None

    def test_missing_footer(self):
        assert extract_tla_from_response("---- MODULE Baz ----\nVARIABLES z") is None

    def test_only_think_block(self):
        assert extract_tla_from_response("<think>nothing</think>") is None


class TestContent:
    def test_has_header_and_footer(self):
        result = extract_tla_from_response(MINIMAL)
        assert result and "----" in result and "====" in result

    def test_result_is_stripped(self):
        result = extract_tla_from_response(f"\n\n  {MINIMAL}  \n\n")
        assert result == result.strip()

    def test_unicode_preserved(self):
        spec = "---- MODULE U ----\nP == ∀ x ∈ {1}: x > 0\n===="
        result = extract_tla_from_response(spec)
        assert result and "∀" in result
