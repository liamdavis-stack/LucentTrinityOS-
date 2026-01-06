from __future__ import annotations

from dataclasses import dataclass
import numpy as np


class Lattice24Projector:
    """
    Interface for a future 24-d lattice projection (e.g., Leech).

    LTOS stance:
      - Keep lattice projection behind an interface.
      - Do not claim Leech correctness until membership + nearest-point tests exist.
    """
    def project(self, state24: np.ndarray) -> np.ndarray:
        raise NotImplementedError


@dataclass(frozen=True)
class NullLattice24Projector(Lattice24Projector):
    """Default projector: no-op."""
    def project(self, state24: np.ndarray) -> np.ndarray:
        return np.array(state24, dtype=complex).reshape(-1)
