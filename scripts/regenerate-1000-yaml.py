import yaml
import os
from enum import Enum, auto
from typing import List, NamedTuple, Tuple


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
    authors: str | None
    # Format YYYY-MM-DD
    date: str | None
    comment: str | None


# Information about a theorem entry: taken from the specification at
# https://github.com/1000-plus/1000-plus.github.io/blob/main/README.md#file-format.
class TheoremEntry(NamedTuple):
    # Wikidata identifier for this theorem (or concept related to the theorem).
    # This is usually the Wikipedia page containing the theorem.
    # FIXME: more typed format? or is this fine?
    wikidata: str # really?
    # disambiguates an entry when two theorems have the same wikidata identifier.
    # X means an extra theorem on a Wikipedia page (e.g. a generalization or special case),
    # A/B/... means different theorems on one Wikipedia page that doesn't have a "main" theorem.
    id_suffix: str | None
    # Our best guess of the MSC-classification. (Should be a two-digit string; not validated.)
    msc_classification: str
    # The exact link to a wikipedia page (or several??)
    wikipedia_links: str
    # Zero or more entries for any formalisation, in any of the proof assistants supported.
    formalisations: List[Tuple[ProofAssistant, FormalisationEntry]]


def _write_entry():
    return "TODO!"

def main():
    dir = "../1000-plus.github.io/_thm"
    files = []
    with os.scandir(dir) as entries:
        for entry in entries:
            if entry.is_file():
                files.append(entry.name)
    entries
    pass

main()
