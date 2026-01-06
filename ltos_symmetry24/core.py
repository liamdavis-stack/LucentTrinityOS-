from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional
import hashlib

import numpy as np

from .golay import LinearCode24, default_golay_like_generator, generate_code_from_generator
from .symmetry import PermutationAction24, default_actions
from .verify import integrity_report, IntegrityReport
from .plugins.lattice import Lattice24Projector, NullLattice24Projector


@dataclass(frozen=True)
class SymmetryState24:
    vector: np.ndarray               # (24,) complex unit vector
    seed: int                        # 32-bit seed used for RNG
    content_hash: str                # hex digest (sha3_512)
    version: str                     # module/version tag
    meta: Dict[str, Any]             # optional metadata


class LTOS_Symmetry24_Core:
    """
    LTOS Symmetry24 Core

    What it IS:
      - Deterministic content -> 24D complex unit vector (state imprint)
      - Verified code-preserving permutation actions (when they actually verify)
      - Canonicalization via symmetry actions
      - Integrity reporting hooks

    What it is NOT (yet):
      - A proven M24 implementation
      - A proven Leech lattice construction / CVP solver
    """

    VERSION = "ltos_symmetry24.v0"

    def __init__(
        self,
        generator_matrix: Optional[np.ndarray] = None,
        actions: Optional[List[PermutationAction24]] = None,
        lattice_projector: Optional[Lattice24Projector] = None,
    ):
        G = default_golay_like_generator() if generator_matrix is None else np.array(generator_matrix, dtype=int)
        self.code: LinearCode24 = generate_code_from_generator(G)

        self.actions: List[PermutationAction24] = default_actions() if actions is None else actions
        self.lattice: Lattice24Projector = NullLattice24Projector() if lattice_projector is None else lattice_projector

    # -------------------------
    # LTOS imprint / sealing
    # -------------------------
    def seal_to_state24(self, content: Any, meta: Optional[Dict[str, Any]] = None) -> SymmetryState24:
        """
        Deterministically map content -> uniform-ish unit vector on S^{47} (as C^24).
        Uses sha3_512(content_str) to seed a RNG.
        """
        s = str(content).encode("utf-8")
        digest = hashlib.sha3_512(s).digest()
        seed = int.from_bytes(digest[:8], "big") % (2**32)
        rng = np.random.default_rng(seed)

        real = rng.standard_normal(24)
        imag = rng.standard_normal(24)
        vec = real + 1j * imag

        n = np.linalg.norm(vec)
        if n < 1e-12:
            vec = np.ones(24, dtype=complex)
            n = np.linalg.norm(vec)

        vec = vec / n
        return SymmetryState24(
            vector=vec.astype(complex),
            seed=int(seed),
            content_hash=hashlib.sha3_512(s).hexdigest(),
            version=self.VERSION,
            meta={} if meta is None else dict(meta),
        )

    # -------------------------
    # Symmetry action + canonicalization
    # -------------------------
    def apply_symmetry(self, state24: np.ndarray, action_idx: int = 0) -> np.ndarray:
        if not self.actions:
            return np.array(state24, dtype=complex).reshape(-1)

        idx = int(action_idx) % len(self.actions)
        return self.actions[idx].apply_to_state(state24)

    def canonicalize(self, state24: np.ndarray, max_actions: Optional[int] = None, rounding: int = 12) -> np.ndarray:
        """
        Try applying each available action, pick canonical representative
        by lexicographic compare of rounded real/imag components.
        """
        s = np.array(state24, dtype=complex).reshape(-1)
        if s.shape[0] != 24:
            raise ValueError("state24 must be length 24.")

        acts = self.actions if max_actions is None else self.actions[:max_actions]
        candidates = [s] + [a.apply_to_state(s) for a in acts]

        def key(v: np.ndarray):
            r = np.round(v.real, rounding)
            im = np.round(v.imag, rounding)
            return tuple(r.tolist() + im.tolist())

      
