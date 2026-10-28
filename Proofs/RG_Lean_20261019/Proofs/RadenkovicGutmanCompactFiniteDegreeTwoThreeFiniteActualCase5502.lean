/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5502 : Family 6 := level6.get ⟨40,by decide⟩
def sourceMap5502 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap5502 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5502_checked : acceptsGraphIso
    (source (graph core5502) (root 6) 2 2) DegreeOneSmallSpectrum1979.graph sourceMap5502=true := by decide +kernel
theorem fusedMap5502_checked : acceptsGraphIso
    (fused (graph core5502) (root 6) 2 2) DegreeOneSmallSpectrum1021.graph fusedMap5502=true := by decide +kernel
theorem certified5502 : Certified (graph core5502) (root 6) 2 2 :=
  of_native_maps core5502 DegreeOneSmallSpectrum1979.graph DegreeOneSmallSpectrum1021.graph
    sourceMap5502 fusedMap5502 sourceMap5502_checked fusedMap5502_checked
    DegreeTwoThreeFiniteComparisons.comparison5502
#print axioms sourceMap5502_checked
#print axioms fusedMap5502_checked
#print axioms certified5502
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
