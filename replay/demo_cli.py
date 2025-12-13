from axioms.conservation import total_conservation
from axioms.continuity import identity_continuity
from validation.validator import OperatorValidator
from operators.omega_delta import apply_omega_delta
from operators.xi_gamma import apply_xi_gamma
import time, json, hashlib
from pathlib import Path

AXIOMS=[total_conservation,identity_continuity]
validator=OperatorValidator(AXIOMS)

def log_receipt(result,ok):
    line={"ts":time.strftime("%Y-%m-%dT%H:%M:%S"),"op":result.meta["symbol"],
          "before":result.before,"after":result.after,"valid":ok}
    Path("registry").mkdir(exist_ok=True)
    Path("registry/ledger.log").write_text(
        (Path("registry/ledger.log").read_text() if Path("registry/ledger.log").exists() else "")+
        json.dumps(line)+"\n")

def digest_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    state={"000":256,"111":256}
    r1=apply_omega_delta(state); ok1=validator.validate(r1); log_receipt(r1,ok1)
    r2=apply_xi_gamma(r1.after); ok2=validator.validate(r2); log_receipt(r2,ok2)
    manifest=Path("registry/manifests/temporal_paradox_manifest.txt")
    manifest.parent.mkdir(parents=True,exist_ok=True)
    manifest.write_text("Ω⁰: GHZ scaffold → {'000':256,'111':256}\n≡ς: 6D override → {'000':240,'111':272}\n")
    sha=digest_file(manifest)
    Path("registry/digest.index").write_text(f"{time.strftime('%Y-%m-%dT%H:%M:%S')} {sha}\n")
    print("Sealed:",sha)

if __name__=="__main__": main()
