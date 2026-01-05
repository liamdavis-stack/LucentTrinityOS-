#!/usr/bin/env python3
import argparse
import sys

from os_stack.kernel import TrinityKernel, KernelPanic


def cmd_boot(_args):
    k = TrinityKernel()
    info = k.boot()
    print(info)


def cmd_status(_args):
    k = TrinityKernel()
    print(k.status())


def cmd_run(args):
    k = TrinityKernel()
    try:
        result = k.dispatch_operator(args.operator, *args.params)
    except KernelPanic as e:
        print(f"[KERNEL PANIC] {e}", file=sys.stderr)
        return 2
    except Exception as e:
        print(f"[ERROR] {e}", file=sys.stderr)
        return 1

    print(result)
    return 0


def cmd_list_operators(_args):
    # Very lightweight: lists python files in src/axiom_engine/operators
    # without importing them.
    import os
    from pathlib import Path

    p = Path("src/axiom_engine/operators")
    if not p.exists():
        print("No operator directory found at src/axiom_engine/operators")
        return 1

    ops = []
    for f in sorted(p.glob("*.py")):
        if f.name.startswith("__"):
            continue
        ops.append(f.stem)

    if not ops:
        print("No operators found.")
        return 0

    for op in ops:
        print(op)
    return 0


def main():
    parser = argparse.ArgumentParser(prog="lucent")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_boot = sub.add_parser("boot", help="Boot the kernel")
    p_boot.set_defaults(func=cmd_boot)

    p_status = sub.add_parser("status", help="Show kernel status")
    p_status.set_defaults(func=cmd_status)

    p_list = sub.add_parser("list-operators", help="List available operators")
    p_list.set_defaults(func=cmd_list_operators)

    p_run = sub.add_parser("run", help="Run an operator by name")
    p_run.add_argument("operator", help="Operator module/function name")
    p_run.add_argument("params", nargs="*", help="Positional params (strings)")
    p_run.set_defaults(func=cmd_run)

    args = parser.parse_args()
    rc = args.func(args)
    raise SystemExit(rc if isinstance(rc, int) else 0)


if __name__ == "__main__":
    main()
