import os
from enum import Enum, auto
from typing import List, NamedTuple

import yaml

"""
This script contains tools for bi-directional synchronisation/regeneration of 1000.yaml.
Mainly, this consists of an internal typed representation of all theorem entries.
The "upstream -> downstream" direction was only used to generate an initial version of 1000.yaml.
The other direction is not implemented yet, but should be useful in the future.
"""


class ProofAssistant(Enum):
    Isabelle = auto()
    HolLight = auto()
    Coq = auto()
    Lean = auto()
    Metamath = auto()
    Mizar = auto()


# The different formalisation statusses: just the statement or also the proof.
class FormalizationStatus(Enum):
    # The statement of a result was formalized (but not its proof yet).
    Statement = auto()
    # The full proof of a result was formalized.
    FullProof = auto()


# In what library does the formalization appear?
class Library(Enum):
    # The standard library ("S")
    StandardLibrary = auto()
    # The main/biggest mathematical library ("L").
    # (afp, hol light outside standard library, mathcomp, mathlib, mml, set.mm, respectively.)
    MainLibrary = auto()
    # External to the main or standard library (e.g., a dedicated repository) ("X")
    External = auto()


class FormalisationEntry(NamedTuple):
    status: FormalizationStatus
    library: Library
    # A URL pointing to the formalization
    # (or a list collecting a list of theorems for a particular proof assistant).
    url: str
    # XXX: this is missing from the README -> clarify if this should replace the URL field for 'std/main library' formalisations!
    identifiers: str | None
    authors: str | None
    # Format YYYY-MM-DD
    date: str | None
    comment: str | None


# Information about a theorem entry: taken from the specification at
# https://github.com/1000-plus/1000-plus.github.io/blob/main/README.md#file-format.
class TheoremEntry(NamedTuple):
    # Wikidata identifier for this theorem (or concept related to the theorem).
    # Valid identifiers start with the latter Q followed by a number; we only save this number.
    wikidata: int
    # disambiguates an entry when two theorems have the same wikidata identifier.
    # X means an extra theorem on a Wikipedia page (e.g. a generalization or special case),
    # A/B/... means different theorems on one Wikipedia page that doesn't have a "main" theorem.
    id_suffix: str | None
    # Our best guess of the MSC-classification. (Should be a two-digit string; not validated.)
    msc_classification: str
    # The exact link to a wikipedia page: format [[Page name]] or [[Wiki-link|Displayed name]].
    wikipedia_links: str
    # Entries about formalizations in any of the supported proof assistants.
    # Several formalization entries for assistant are allowed.
    formalisations: dict[ProofAssistant, List[FormalisationEntry]]


def _parse_formalization_entry(entry: dict) -> FormalisationEntry:
    form = {
        "formalized": FormalizationStatus.FullProof,
        "statement": FormalizationStatus.Statement,
    }
    status = form[entry["status"]]
    lib = {
        "S": Library.StandardLibrary,
        "L": Library.MainLibrary,
        "X": Library.External,
    }
    library = lib[entry["library"]]
    return FormalisationEntry(
        status, library, entry["url"], entry.get("identifiers"), entry.get("authors"), entry.get("date"), entry.get("comment")
    )


def _parse_wikidata(input: str) -> int | None:
    if not input.startswith("Q"):
        print(f"error: invalid wikidata identifier {input}; must start with a letter 'Q'")
        return None
    try:
        return int(input.removeprefix("Q"))
    except ValueError:
        print("invalid input: {input} must be the letter 'Q', followed by a number")
        return None


# Return a human-ready theorem title, as well as a `TheoremEntry` with the underlying data.
# Return `None` if `contents` does not describe a valid theorem entry.
def _parse_theorem_entry(contents: List[str]) -> TheoremEntry | None:
    assert contents[0].rstrip() == "---"
    assert contents[-1].rstrip() == "---"
    # For optics, we check that all entry files start with the theorem name as comment.
    # We parse the actual title from the wikipedia data below: this yields virtually the same results.
    assert contents[1].startswith("# ") or contents[1].startswith("## ")
    data = yaml.safe_load("".join(contents[1:-1]))
    wikidata = _parse_wikidata(data["wikidata"])
    if wikidata is None:
        return None
    provers: dict[str, ProofAssistant] = {
        "isabelle": ProofAssistant.Isabelle,
        "hol_light": ProofAssistant.HolLight,
        "coq": ProofAssistant.Coq,
        "lean": ProofAssistant.Lean,
        "metamath": ProofAssistant.Metamath,
        "mizar": ProofAssistant.Mizar,
    }
    formalisations = dict()
    for pname, variant in provers.items():
        if pname in data:
            entries = [_parse_formalization_entry(entry) for entry in data[pname]]
            formalisations[variant] = entries
        else:
            formalisations[variant] = []

    res = TheoremEntry(
        wikidata, data.get("id_suffix"), data["msc_classification"],
        data["wikipedia_links"], formalisations
    )
    return res


def _parse_title(entry: TheoremEntry) -> str:
    # FIXME: what's the best way to deal with multiple links here?
    # For now, let's match the webpage and just show the first link's target.
    # if len(entry.wikipedia_links) > 1:
    #     print(f"attention: found several wikipedia links for a theorem: {entry.wikipedia_links}")
    # Handle wikipedia links [[Big theorem]]s also.
    (title, _, suf) = entry.wikipedia_links[0].removeprefix("[[").partition("]]")
    if suf == "s":
        title += "s"
    if "|" in title:
        title = title.partition("|")[2]
    return title


def _write_entry(entry: TheoremEntry) -> str:
    inner = {"title": _parse_title(entry)}
    form = entry.formalisations[ProofAssistant.Lean]
    if form:
        # If there are several formalisations, we prioritise mathlib and stdlib
        # formalisations over external projects.
        # If there are still several, we pick the first in the theorem file.
        stdlib_formalisations = [f for f in form if f.library == Library.StandardLibrary]
        mathlib_formalisations = [f for f in form if f.library == Library.MainLibrary]
        if stdlib_formalisations:
            first = stdlib_formalisations[0]
            if first.identifiers is not None:
                if len(first.identifiers) == 1:
                    inner["decl"] = first.identifiers[0]
                else:
                    inner["decls"] = first.identifiers
        elif mathlib_formalisations:
            first = mathlib_formalisations[0]
            if first.identifiers is not None:
                if len(first.identifiers) == 1:
                    inner["decl"] = first.identifiers[0]
                else:
                    inner["decls"] = first.identifiers
        else:
            first = form[0]
            assert first.library == Library.External  # internal consistency check
            inner["url"] = first.url
            # One *could* also write out the identifier(s) of the relevant theorems:
            # since this cannot easily be checked, we don't do so.
        if first.authors:
            inner["author"] = " and ".join(first.authors)
        # Add additional metadata, so no information is lost in the generated yaml file.
        if first.date:
            inner['date'] = first.date
        if first.comment:
            inner['comment'] = first.comment
    key = f"Q{entry.wikidata}" + (entry.id_suffix or "")
    res = {key: inner}
    return yaml.dump(res, sort_keys=False)


def regenerate_from_upstream(_args) -> None:
    # FIXME: download the upstream files to a local directory; or
    # if the --local option and a location are passed, look in that location instead.
    # For now, the latter is used, with a hard-coded directory...
    dir = "../1000-plus.github.io/_thm"
    # Determine the list of theorem entry files.
    theorem_entry_files = []
    with os.scandir(dir) as entries:
        theorem_entry_files = [entry.name for entry in entries if entry.is_file()]
    # Parse each entry file into a theorem entry.
    thms: List[TheoremEntry | None] = []
    for file in theorem_entry_files:
        with open(os.path.join(dir, file), "r") as f:
            thms.append(_parse_theorem_entry(f.readlines()))
    # Sort alphabetically according to wikidata ID.
    # FUTURE: also use MSC classification?
    filtered = filter(lambda t: t is not None, thms)

    # Write out a new yaml file for this, again.
    with open(os.path.join("docs", "1000.yaml"), "w") as f:
        f.write("\n".join([_write_entry(thm) for thm in sorted(filtered, key=lambda t: t.wikidata)]))


if __name__ == "__main__":
    import sys

    regenerate_from_upstream(sys.argv)
