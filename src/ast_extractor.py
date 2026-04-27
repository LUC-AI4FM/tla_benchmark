from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Optional

sys.path.insert(0, str(Path(__file__).parent))

from utils import data_dir, get_logger, load_json, repo_root, save_json

logger = get_logger("ast_extractor")

_BUILTIN_NAMES: dict[int, str] = {
    154: "=", 157: "/=",
    175: "/\\", 233: "/\\",
    176: "\\/", 234: "\\/",
    177: "~", 178: "=>", 179: "<=>",
    180: "TRUE", 181: "FALSE",
    182: "\\A", 183: "\\E", 184: "CHOOSE",
    185: "\\in", 186: "\\notin",
    187: "\\cup", 188: "\\cap", 189: "\\subseteq",
    190: "SUBSET", 191: "UNION", 256: "SetEnumerate",
    195: "FcnConstructor", 196: "FcnApplication",
    197: "DOMAIN", 198: "EXCEPT",
    199: "<<>>", 200: "RecordConstructor", 201: "RecordAccess",
    202: "+", 203: "-", 204: "*", 205: "\\div",
    206: "%", 207: "^", 208: "..", 209: "UnaryMinus",
    210: "<", 211: ">", 212: "<=", 213: ">=",
    214: "[]", 215: "<>", 216: "~>", 217: "-+->",
    218: "ENABLED", 219: "UNCHANGED", 220: "ACTION",
    221: "WF_", 222: "SF_",
    223: "IF", 224: "CASE", 225: "LET", 226: "STRING",
    192: "\\X", 193: "|->", 194: "->",
}

_STDLIB_NAMES = {
    "Naturals", "Integers", "Reals", "Sequences", "FiniteSets",
    "Bags", "TLC", "TLAPS", "--TLA+ BUILTINS--",
    "Functions", "SequencesExt", "FiniteSetTheorems", "WellFoundedInduction",
    "NaturalsInduction", "IOUtils", "CSV", "SVG", "Json", "TLCExt",
    "Randomization", "Toolbox", "Apalache", "Statistics",
    "BagsExt", "Folds", "Relation", "Graphs", "UndirectedGraphs",
}


class SANYParser:
    def __init__(self, xml_root: ET.Element, module_name: str) -> None:
        self.root = xml_root
        self.module_name = module_name
        self.uid_table: dict[int, dict[str, Any]] = {}
        self._build_uid_table()

    def _build_uid_table(self) -> None:
        context = self.root.find("context")
        if context is None:
            return

        for entry in context.findall("entry"):
            uid_elem = entry.find("UID")
            if uid_elem is None or uid_elem.text is None:
                continue
            uid = int(uid_elem.text)

            for child in entry:
                if child.tag != "UID":
                    loc = child.find("location")
                    if loc is not None:
                        fn_elem = loc.find("filename")
                        if fn_elem is not None and fn_elem.text in _STDLIB_NAMES:
                            break

                    self.uid_table[uid] = self._parse_context_entry(uid, child)
                    break

    def _parse_context_entry(self, uid: int, elem: ET.Element) -> dict[str, Any]:
        tag = elem.tag
        name_elem = elem.find("uniquename")
        name = name_elem.text if name_elem is not None and name_elem.text else f"UID_{uid}"

        arity_elem = elem.find("arity")
        arity = int(arity_elem.text) if arity_elem is not None and arity_elem.text else 0

        result: dict[str, Any] = {
            "uid": uid, "kind": tag, "name": name, "arity": arity,
        }

        if tag == "OpDeclNode":
            kind_elem = elem.find("kind")
            if kind_elem is not None and kind_elem.text:
                result["decl_kind"] = int(kind_elem.text)

        if tag == "UserDefinedOpKind":
            body_elem = elem.find("body")
            if body_elem is not None and len(body_elem) > 0:
                result["body"] = self._parse_expr(body_elem[0])

            params = elem.find("params")
            if params is not None:
                result["params"] = [self._ref_name(p) for p in params]

        return result

    def _ref_name(self, elem: ET.Element) -> str:
        for child in elem:
            if child.tag.endswith("Ref"):
                uid_elem = child.find("UID")
                if uid_elem is not None and uid_elem.text is not None:
                    uid = int(uid_elem.text)
                    if uid in self.uid_table:
                        return self.uid_table[uid].get("name", f"UID_{uid}")
                    if uid in _BUILTIN_NAMES:
                        return _BUILTIN_NAMES[uid]
                    return f"UID_{uid}"
        return elem.text or "unknown"

    def _parse_expr(self, elem: ET.Element) -> dict[str, Any]:
        tag = elem.tag

        if tag == "OpApplNode":
            return self._parse_op_apply(elem)
        elif tag == "NumeralNode":
            val_elem = elem.find("IntValue")
            val = int(val_elem.text) if val_elem is not None and val_elem.text else 0
            return {"type": "Numeral", "value": val}
        elif tag == "DecimalNode":
            val_elem = elem.find("DecValue")
            val = val_elem.text if val_elem is not None else "0.0"
            return {"type": "Decimal", "value": val}
        elif tag == "StringNode":
            val_elem = elem.find("StringValue")
            val = val_elem.text if val_elem is not None else ""
            return {"type": "String", "value": val}
        elif tag == "AtNode":
            return {"type": "At"}
        elif tag == "LetInNode":
            return self._parse_let_in(elem)
        elif tag == "SubstInNode":
            body = elem.find("body")
            if body is not None and len(body) > 0:
                return self._parse_expr(body[0])
            return {"type": "SubstIn"}
        else:
            children = [self._parse_expr(c) for c in elem if c.tag not in ("location", "level", "UID")]
            if len(children) == 1:
                return children[0]
            elif children:
                return {"type": tag, "children": children}
            return {"type": tag}

    def _parse_op_apply(self, elem: ET.Element) -> dict[str, Any]:
        operator_elem = elem.find("operator")
        op_name = "unknown"

        if operator_elem is not None:
            for ref in operator_elem:
                if ref.tag.endswith("Ref"):
                    uid_elem = ref.find("UID")
                    if uid_elem is not None and uid_elem.text is not None:
                        uid = int(uid_elem.text)
                        if uid in _BUILTIN_NAMES:
                            op_name = _BUILTIN_NAMES[uid]
                        elif uid in self.uid_table:
                            op_name = self.uid_table[uid].get("name", f"UID_{uid}")
                        else:
                            op_name = f"UID_{uid}"

        operands_elem = elem.find("operands")
        operands: list[dict[str, Any]] = []
        if operands_elem is not None:
            for child in operands_elem:
                if child.tag not in ("location", "level"):
                    operands.append(self._parse_expr(child))

        bounds: list[dict[str, Any]] = []
        for bs in elem.findall("boundSymbols"):
            for fp in bs:
                if fp.tag.endswith("Ref"):
                    uid_elem = fp.find("UID")
                    if uid_elem is not None and uid_elem.text is not None:
                        uid = int(uid_elem.text)
                        name = self.uid_table.get(uid, {}).get("name", f"UID_{uid}")
                        bounds.append({"name": name})

        result: dict[str, Any] = {"type": "Apply", "operator": op_name}

        if bounds:
            result["bound_vars"] = [b["name"] for b in bounds]
        if operands:
            result["operands"] = operands

        if op_name in ("/\\", "\\/") and operands:
            result["type"] = "Conjunction" if op_name == "/\\" else "Disjunction"
            del result["operator"]
        elif op_name == "=":
            result["type"] = "Equality"
            del result["operator"]
        elif op_name in ("\\A", "\\E"):
            result["type"] = "Universal" if op_name == "\\A" else "Existential"
            del result["operator"]
        elif op_name in ("[]", "<>", "~>"):
            result["type"] = {"[]": "Always", "<>": "Eventually", "~>": "LeadsTo"}[op_name]
            del result["operator"]
        elif op_name == "IF":
            result["type"] = "IfThenElse"
            del result["operator"]
        elif op_name == "CASE":
            result["type"] = "Case"
            del result["operator"]
        elif op_name in ("WF_", "SF_"):
            result["type"] = "WeakFairness" if op_name == "WF_" else "StrongFairness"
            del result["operator"]
        elif op_name == "UNCHANGED":
            result["type"] = "Unchanged"
            del result["operator"]
        elif op_name == "ENABLED":
            result["type"] = "Enabled"
            del result["operator"]
        elif op_name == "'":
            result["type"] = "Prime"
            del result["operator"]

        return result

    def _parse_let_in(self, elem: ET.Element) -> dict[str, Any]:
        result: dict[str, Any] = {"type": "LetIn"}

        let_defs: list[dict[str, Any]] = []
        for opdef in elem.findall("opDefs"):
            for child in opdef:
                name_elem = child.find("uniquename")
                name = name_elem.text if name_elem is not None else "unknown"
                body_elem = child.find("body")
                body = None
                if body_elem is not None and len(body_elem) > 0:
                    body = self._parse_expr(body_elem[0])
                let_defs.append({"name": name, "body": body})

        if let_defs:
            result["definitions"] = let_defs

        body_elem = elem.find("body")
        if body_elem is not None and len(body_elem) > 0:
            result["body"] = self._parse_expr(body_elem[0])

        return result

    def build_module_ast(self) -> dict[str, Any]:
        module: dict[str, Any] = {
            "type": "Module",
            "name": self.module_name,
            "children": [],
        }

        extends: list[str] = []
        constants: list[str] = []
        variables: list[str] = []
        assumptions: list[dict[str, Any]] = []
        theorems: list[dict[str, Any]] = []
        operator_defs: list[dict[str, Any]] = []

        for uid, entry in sorted(self.uid_table.items()):
            kind = entry.get("kind", "")
            name = entry.get("name", "")

            if kind in ("BuiltInKind", "ModuleNode"):
                continue

            if kind == "OpDeclNode":
                decl_kind = entry.get("decl_kind")
                if decl_kind == 2:
                    constants.append(name)
                elif decl_kind == 3:
                    variables.append(name)
            elif kind == "FormalParamNode":
                continue
            elif kind == "UserDefinedOpKind":
                op_node: dict[str, Any] = {"type": "OperatorDef", "name": name}
                if "params" in entry:
                    op_node["params"] = entry["params"]
                if "body" in entry:
                    op_node["body"] = entry["body"]
                operator_defs.append(op_node)
            elif kind == "AssumeNode":
                assumptions.append({"type": "Assumption", "name": name, "body": entry.get("body")})
            elif kind == "TheoremNode":
                theorems.append({"type": "Theorem", "name": name, "body": entry.get("body")})

        if extends:
            module["children"].append({"type": "Extends", "modules": extends})
        if constants:
            module["children"].append({"type": "Constants", "names": constants})
        if variables:
            module["children"].append({"type": "Variables", "names": variables})
        for a in assumptions:
            module["children"].append(a)
        for op in operator_defs:
            module["children"].append(op)
        for t in theorems:
            module["children"].append(t)

        return module


def _find_java() -> str:
    for candidate in ["java", "/usr/bin/java", "/usr/local/bin/java"]:
        try:
            result = subprocess.run(
                [candidate, "-version"],
                capture_output=True, text=True, timeout=10,
            )
            if result.returncode == 0 or "version" in (result.stderr + result.stdout):
                return candidate
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass

    java = shutil.which("java")
    if java:
        return java
    raise EnvironmentError("Java not found. Install JDK 11+ for SANY.")


def extract_ast_xml(tla_path: str, module_name: str) -> Optional[str]:
    java = _find_java()
    jar = str(repo_root() / "tla2tools.jar")
    community_jar = str(repo_root() / "CommunityModules-deps.jar")
    classpath = f"{jar}:{community_jar}" if os.path.exists(community_jar) else jar

    with tempfile.TemporaryDirectory() as tmpdir:
        formallm_data = Path.home() / "Downloads" / "FormaLLM-main 2" / "data"
        if formallm_data.exists():
            for tla_file in formallm_data.rglob("*.tla"):
                dest = os.path.join(tmpdir, tla_file.name)
                if not os.path.exists(dest):
                    shutil.copy2(str(tla_file), dest)
        else:
            tla_dir = data_dir() / "tla_files"
            v2_dir = data_dir() / "v2_json"
            for src_file in tla_dir.glob("*.tla"):
                spec_id_str = src_file.stem
                v2_path = v2_dir / f"{spec_id_str}.json"
                if v2_path.exists():
                    try:
                        v2_data = load_json(v2_path)
                        mod_name = v2_data.get("ModuleName", spec_id_str)
                    except Exception:
                        mod_name = spec_id_str
                else:
                    mod_name = spec_id_str
                dest = os.path.join(tmpdir, f"{mod_name}.tla")
                if not os.path.exists(dest):
                    shutil.copy2(str(src_file), dest)

        target = os.path.join(tmpdir, f"{module_name}.tla")
        if not os.path.exists(target):
            shutil.copy2(tla_path, target)

        cmd = [java, "-cp", classpath, "tla2sany.xml.XMLExporter", target]
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=120,
            )
            if result.returncode != 0 and "<?xml" not in result.stdout:
                logger.warning(
                    "SANY failed for %s: %s",
                    module_name,
                    result.stderr[:200] or result.stdout[:200],
                )
                return None
            return result.stdout
        except subprocess.TimeoutExpired:
            logger.warning("SANY timed out for %s", module_name)
            return None
        except Exception as exc:
            logger.error("SANY error for %s: %s", module_name, exc)
            return None


def extract_ast(tla_path: str, module_name: str) -> Optional[dict[str, Any]]:
    xml_str = extract_ast_xml(tla_path, module_name)
    if xml_str is None:
        return None

    try:
        root = ET.fromstring(xml_str)
    except ET.ParseError as exc:
        logger.error("XML parse error for %s: %s", module_name, exc)
        return None

    parser = SANYParser(root, module_name)
    return parser.build_module_ast()


def extract_all(
    spec_ids: Optional[list[int]] = None,
    output_dir: Optional[Path] = None,
) -> dict[str, Any]:
    if output_dir is None:
        output_dir = data_dir() / "ast_json"
    output_dir.mkdir(parents=True, exist_ok=True)

    tla_dir = data_dir() / "tla_files"
    v2_dir = data_dir() / "v2_json"

    if spec_ids is None:
        spec_ids = sorted(
            int(f.stem) for f in v2_dir.glob("*.json") if f.stem.isdigit()
        )

    stats = {"total": len(spec_ids), "success": 0, "failed": 0, "skipped": 0}

    for spec_id in spec_ids:
        tla_path = tla_dir / f"{spec_id}.tla"
        v2_path = v2_dir / f"{spec_id}.json"

        if not tla_path.exists():
            logger.warning("spec=%d: .tla file not found, skipping", spec_id)
            stats["skipped"] += 1
            continue

        if not v2_path.exists():
            logger.warning("spec=%d: v2 JSON not found, skipping", spec_id)
            stats["skipped"] += 1
            continue

        v2_data = load_json(v2_path)
        module_name = v2_data.get("ModuleName", str(spec_id))

        ast = extract_ast(str(tla_path), module_name)

        if ast is None:
            logger.warning("spec=%d (%s): extraction failed", spec_id, module_name)
            stats["failed"] += 1
            continue

        ast["spec_id"] = spec_id
        ast["source_file"] = f"{spec_id}.tla"

        save_json(ast, output_dir / f"{spec_id}.json")
        stats["success"] += 1

        if stats["success"] % 20 == 0:
            logger.info(
                "progress: %d/%d (%.0f%%)",
                stats["success"], stats["total"],
                100 * stats["success"] / stats["total"],
            )

    logger.info(
        "done: %d success, %d failed, %d skipped (of %d)",
        stats["success"], stats["failed"], stats["skipped"], stats["total"],
    )

    save_json(stats, output_dir / "_extraction_stats.json")
    return stats


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract ASTs from TLA+ files via SANY.")
    parser.add_argument("--spec_id", type=int, default=None)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--backup", action="store_true")
    args = parser.parse_args()

    ast_dir = data_dir() / "ast_json"
    if args.backup and ast_dir.exists():
        backup_dir = data_dir() / "ast_json_flat_backup"
        if not backup_dir.exists():
            shutil.copytree(ast_dir, backup_dir)
            logger.info("backed up ast_json/ to %s", backup_dir)

    spec_ids = None
    if args.spec_id is not None:
        spec_ids = [args.spec_id]
    elif args.limit is not None:
        v2_dir = data_dir() / "v2_json"
        all_ids = sorted(int(f.stem) for f in v2_dir.glob("*.json") if f.stem.isdigit())
        spec_ids = all_ids[: args.limit]

    stats = extract_all(spec_ids=spec_ids)
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
