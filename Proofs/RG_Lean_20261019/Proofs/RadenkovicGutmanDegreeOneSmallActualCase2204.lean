/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2204 : Family 10 := level10.get ⟨717,by decide⟩
def sourceMap2204 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2204 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2204_checked : acceptsGraphIso
    (source (graph core2204) (root 10) 0 0) DegreeOneSmallSpectrum1788.graph sourceMap2204=true := by decide +kernel
theorem fusedMap2204_checked : acceptsGraphIso
    (fused (graph core2204) (root 10) 0 0) DegreeOneSmallSpectrum1344.graph fusedMap2204=true := by decide +kernel
theorem certified2204 : Certified (graph core2204) (root 10) 0 0 :=
  of_native_maps core2204 DegreeOneSmallSpectrum1788.graph DegreeOneSmallSpectrum1344.graph
    sourceMap2204 fusedMap2204 sourceMap2204_checked fusedMap2204_checked
    DegreeOneSmallComparisons.comparison2204
#print axioms sourceMap2204_checked
#print axioms fusedMap2204_checked
#print axioms certified2204
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
