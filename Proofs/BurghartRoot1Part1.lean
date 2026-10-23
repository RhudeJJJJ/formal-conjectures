import Proofs.BurghartFringeData
/-! # Root 1 leaf-subset class 1 -/
set_option Elab.async false
set_option maxRecDepth 100000
namespace BurghartLists
open BurghartCertificate
set_option maxHeartbeats 0 in
theorem root1_part1 : norm1 (fringePart T1 distances1 0 1) = rootParts1 1 := by decide +kernel
#print axioms root1_part1
end BurghartLists
