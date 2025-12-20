import matplotlib.pyplot as plt

def plot_lineage(commits, operators, manifests):
    fig, ax = plt.subplots(figsize=(8,6))

    # Plot commit lineage
    ax.plot(range(len(commits)), [i+1 for i in range(len(commits))],
            marker='o', label="Commits")

    # Plot operator count growth
    ax.plot(range(len(operators)), operators,
            marker='s', label="Operators")

    # Plot manifest count growth
    ax.plot(range(len(manifests)), manifests,
            marker='^', label="Manifests")

    ax.set_title("LucentTrinityOS✝️ Lineage Growth")
    ax.set_xlabel("Index")
    ax.set_ylabel("Count")
    ax.legend()
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    commits = [
        "Genesis",
        "QuantumCross",
        "OperatorAxioms",
        "Registry Manifest",
        "Resurrection"
    ]
    operators = [0, 1, 2, 3, 5]   # growth of operator canon
    manifests = [0, 1, 2, 4, 6]   # registry receipts sealed

    plot_lineage(commits, operators, manifests)
