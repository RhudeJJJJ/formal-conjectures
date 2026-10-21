/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2260 : Family 10 := level10.get ⟨841,by decide⟩
def sourceMap2260 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2260 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2260_checked : acceptsGraphIso
    (source (graph core2260) (root 10) 0 0) DegreeOneSmallSpectrum1834.graph sourceMap2260=true := by decide +kernel
theorem fusedMap2260_checked : acceptsGraphIso
    (fused (graph core2260) (root 10) 0 0) DegreeOneSmallSpectrum1466.graph fusedMap2260=true := by decide +kernel
theorem certified2260 : Certified (graph core2260) (root 10) 0 0 :=
  of_native_maps core2260 DegreeOneSmallSpectrum1834.graph DegreeOneSmallSpectrum1466.graph
    sourceMap2260 fusedMap2260 sourceMap2260_checked fusedMap2260_checked
    DegreeOneSmallComparisons.comparison2260
#print axioms sourceMap2260_checked
#print axioms fusedMap2260_checked
#print axioms certified2260
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
