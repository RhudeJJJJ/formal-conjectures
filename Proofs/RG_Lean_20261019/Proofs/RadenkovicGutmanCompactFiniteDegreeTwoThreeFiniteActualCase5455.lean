/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5455 : Family 7 := level7.get ⟨108,by decide⟩
def sourceMap5455 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap5455 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap5455_checked : acceptsGraphIso
    (source (graph core5455) (root 7) 0 0) SmallGeFourSpectrum031.graph sourceMap5455=true := by decide +kernel
theorem fusedMap5455_checked : acceptsGraphIso
    (fused (graph core5455) (root 7) 0 0) DegreeOneSmallSpectrum161.graph fusedMap5455=true := by decide +kernel
theorem certified5455 : Certified (graph core5455) (root 7) 0 0 :=
  of_native_maps core5455 SmallGeFourSpectrum031.graph DegreeOneSmallSpectrum161.graph
    sourceMap5455 fusedMap5455 sourceMap5455_checked fusedMap5455_checked
    DegreeTwoThreeFiniteComparisons.comparison5455
#print axioms sourceMap5455_checked
#print axioms fusedMap5455_checked
#print axioms certified5455
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
