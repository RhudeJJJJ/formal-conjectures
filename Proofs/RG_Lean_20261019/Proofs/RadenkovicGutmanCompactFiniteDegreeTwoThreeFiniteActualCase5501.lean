/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5501 : Family 6 := level6.get ⟨35,by decide⟩
def sourceMap5501 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,10,11,12,4,5,6,7,8,9] (sourceLabel 6 2 2 v)
def fusedMap5501 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5501_checked : acceptsGraphIso
    (source (graph core5501) (root 6) 2 2) DegreeOneSmallSpectrum1974.graph sourceMap5501=true := by decide +kernel
theorem fusedMap5501_checked : acceptsGraphIso
    (fused (graph core5501) (root 6) 2 2) DegreeOneSmallSpectrum947.graph fusedMap5501=true := by decide +kernel
theorem certified5501 : Certified (graph core5501) (root 6) 2 2 :=
  of_native_maps core5501 DegreeOneSmallSpectrum1974.graph DegreeOneSmallSpectrum947.graph
    sourceMap5501 fusedMap5501 sourceMap5501_checked fusedMap5501_checked
    DegreeTwoThreeFiniteComparisons.comparison5501
#print axioms sourceMap5501_checked
#print axioms fusedMap5501_checked
#print axioms certified5501
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
