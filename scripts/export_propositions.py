"""Refresh proof-prompt theorem signatures from the checked Book sources."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent


def main():
    propositions = {}
    for index in range(1, 49):
        source = (ROOT / "Book" / f"Prop{index:02d}.lean").read_text()
        declarations = re.findall(r"^theorem\s+(proposition_\d+'*)\s*:\s*(.*?)\s*:=", source, re.M | re.S)
        if not declarations or len(declarations) != len(re.findall(r"^theorem\s", source, re.M)):
            raise ValueError(f"Could not extract every theorem in Prop{index:02d}.lean")
        propositions[str(index)] = [name + " : " + " ".join(statement.split()) for name, statement in declarations]
    directory = ROOT / "AutoFormalization" / "proof"
    (directory / "book_propositions.json").write_text(json.dumps(propositions, ensure_ascii=False, indent=4) + "\n")
    path = directory / "unigeo_instruction.txt"
    head, rest = path.read_text().split("-- Propositions from Euclid's Elements Book I --\n", 1)
    old, tail = rest.split("\n-- Proof Tactics --", 1)
    selected = {int(i) for i in re.findall(r"proposition_(\d+)", old)}
    declarations = ["axiom " + declaration for index in sorted(selected) for declaration in propositions[str(index)]]
    path.write_text(head + "-- Propositions from Euclid's Elements Book I --\n" + "\n".join(declarations) + "\n\n-- Proof Tactics --" + tail)
    print(f"Exported {sum(map(len, propositions.values()))} checked theorem signatures.")


if __name__ == "__main__":
    main()
