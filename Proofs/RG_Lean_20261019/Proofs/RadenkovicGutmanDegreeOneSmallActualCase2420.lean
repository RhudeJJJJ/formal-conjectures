/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2420 : Family 10 := level10.get ⟨1305,by decide⟩
def sourceMap2420 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2420 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2420_checked : acceptsGraphIso
    (source (graph core2420) (root 10) 0 0) DegreeOneSmallSpectrum1943.graph sourceMap2420=true := by decide +kernel
theorem fusedMap2420_checked : acceptsGraphIso
    (fused (graph core2420) (root 10) 0 0) DegreeOneSmallSpectrum1942.graph fusedMap2420=true := by decide +kernel
theorem certified2420 : Certified (graph core2420) (root 10) 0 0 :=
  of_native_maps core2420 DegreeOneSmallSpectrum1943.graph DegreeOneSmallSpectrum1942.graph
    sourceMap2420 fusedMap2420 sourceMap2420_checked fusedMap2420_checked
    DegreeOneSmallComparisons.comparison2420
#print axioms sourceMap2420_checked
#print axioms fusedMap2420_checked
#print axioms certified2420
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
