/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5503 : Family 6 := level6.get ⟨42,by decide⟩
def sourceMap5503 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap5503 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5503_checked : acceptsGraphIso
    (source (graph core5503) (root 6) 2 2) DegreeOneSmallSpectrum1981.graph sourceMap5503=true := by decide +kernel
theorem fusedMap5503_checked : acceptsGraphIso
    (fused (graph core5503) (root 6) 2 2) DegreeOneSmallSpectrum1095.graph fusedMap5503=true := by decide +kernel
theorem certified5503 : Certified (graph core5503) (root 6) 2 2 :=
  of_native_maps core5503 DegreeOneSmallSpectrum1981.graph DegreeOneSmallSpectrum1095.graph
    sourceMap5503 fusedMap5503 sourceMap5503_checked fusedMap5503_checked
    DegreeTwoThreeFiniteComparisons.comparison5503
#print axioms sourceMap5503_checked
#print axioms fusedMap5503_checked
#print axioms certified5503
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
