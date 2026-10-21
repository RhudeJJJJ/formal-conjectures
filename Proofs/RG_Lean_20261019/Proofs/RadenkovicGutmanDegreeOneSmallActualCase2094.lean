/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2094 : Family 10 := level10.get ⟨509,by decide⟩
def sourceMap2094 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 10 0 0 v)
def fusedMap2094 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2094_checked : acceptsGraphIso
    (source (graph core2094) (root 10) 0 0) DegreeOneSmallSpectrum1591.graph sourceMap2094=true := by decide +kernel
theorem fusedMap2094_checked : acceptsGraphIso
    (fused (graph core2094) (root 10) 0 0) DegreeOneSmallSpectrum997.graph fusedMap2094=true := by decide +kernel
theorem certified2094 : Certified (graph core2094) (root 10) 0 0 :=
  of_native_maps core2094 DegreeOneSmallSpectrum1591.graph DegreeOneSmallSpectrum997.graph
    sourceMap2094 fusedMap2094 sourceMap2094_checked fusedMap2094_checked
    DegreeOneSmallComparisons.comparison2094
#print axioms sourceMap2094_checked
#print axioms fusedMap2094_checked
#print axioms certified2094
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
