/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2280 : Family 10 := level10.get ⟨883,by decide⟩
def sourceMap2280 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,0,7,8,9,10,11,12,1,2,3,5,6] (sourceLabel 10 0 0 v)
def fusedMap2280 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2280_checked : acceptsGraphIso
    (source (graph core2280) (root 10) 0 0) DegreeOneSmallSpectrum1473.graph sourceMap2280=true := by decide +kernel
theorem fusedMap2280_checked : acceptsGraphIso
    (fused (graph core2280) (root 10) 0 0) DegreeOneSmallSpectrum1461.graph fusedMap2280=true := by decide +kernel
theorem certified2280 : Certified (graph core2280) (root 10) 0 0 :=
  of_native_maps core2280 DegreeOneSmallSpectrum1473.graph DegreeOneSmallSpectrum1461.graph
    sourceMap2280 fusedMap2280 sourceMap2280_checked fusedMap2280_checked
    DegreeOneSmallComparisons.comparison2280
#print axioms sourceMap2280_checked
#print axioms fusedMap2280_checked
#print axioms certified2280
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
