"""
Compatibility layer.

Historically tests imported operators from `src.operators.*`.
The canonical implementations now live under `src.axiom_engine.operators`.
This package preserves the old import path to keep CI and legacy code stable.
"""
