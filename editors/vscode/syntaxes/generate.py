#!/usr/bin/env python3
"""Generate the TextMate grammars, one per language, from a few shared patterns.

Run from this directory: python3 generate.py
"""
import json
import os

NAME = r"[^\s()\[\].:λΛΠ∀→|*□⋆+]+"


def grammar(lang, decls, binders, sorts, extra=()):
    pats = []
    for kw, scope in decls:
        pats.append({"match": rf"\b({kw})\s+({NAME})",
                     "captures": {"1": {"name": f"keyword.other.declaration.{lang}"},
                                  "2": {"name": f"{scope}.{lang}"}}})
    if binders:
        pats.append({"match": rf"({'|'.join(binders)})\s*({NAME})",
                     "captures": {"1": {"name": f"keyword.operator.binder.{lang}"},
                                  "2": {"name": f"variable.parameter.{lang}"}}})
    pats += list(extra)
    if sorts:
        pats.append({"match": "|".join(sorts), "name": f"support.type.sort.{lang}"})
    pats += [
        {"match": ":=", "name": f"keyword.operator.assignment.{lang}"},
        {"match": "→", "name": f"keyword.operator.arrow.{lang}"},
        {"match": "[:.]", "name": f"punctuation.separator.{lang}"},
    ]
    return {"$schema": "https://raw.githubusercontent.com/martinring/tmlanguage/master/tmlanguage.json",
            "name": lang, "scopeName": f"source.{lang}", "patterns": pats}


FN, TY = "entity.name.function", "entity.name.type"
LANGS = {
    "stlc": grammar("stlc", [("def", FN)], ["λ"], ["⋆"],
                    [{"match": r"\?\d+|(?<![\w])_(?![\w])",
                      "name": "variable.language.metavariable.stlc"}]),
    "systemf": grammar("systemf", [("def", FN), ("type", TY)], ["λ", "Λ", "∀"], [],
                       [{"match": r"\[|\]", "name": "punctuation.section.brackets.systemf"}]),
    "coc": grammar("coc", [("def", FN)], ["λ", "Π"], [r"\*", "□"]),
    "coic": grammar("coic", [("def", FN), ("inductive", TY)], ["λ", "Π"], [r"\*", "□"],
                    [{"match": r"\b\w+_rec\b", "name": "support.function.recursor.coic"},
                     {"match": r"\|", "name": "punctuation.separator.constructor.coic"}]),
    "ecc": grammar("ecc", [("def", FN)], ["λ", "Π"], [r"\bProp\b", r"\bType\b"],
                   [{"match": r"(?<=\bType)\s+\d+\b", "name": "constant.numeric.level.ecc"}]),
    "float": grammar("float", [("float", "variable.other.constant")], [], [],
                     [{"match": r"\b\d+(\.\d+)?\b", "name": "constant.numeric.float"},
                      {"match": r"[+*]", "name": "keyword.operator.arithmetic.float"}]),
}

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    for name, g in LANGS.items():
        with open(os.path.join(here, f"{name}.tmLanguage.json"), "w") as f:
            json.dump(g, f, indent=2, ensure_ascii=False)
            f.write("\n")
