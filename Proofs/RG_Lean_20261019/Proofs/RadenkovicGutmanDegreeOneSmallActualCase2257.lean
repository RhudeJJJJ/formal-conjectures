/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2257 : Family 10 := level10.get ⟨835,by decide⟩
def sourceMap2257 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2257 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2257_checked : acceptsGraphIso
    (source (graph core2257) (root 10) 0 0) DegreeOneSmallSpectrum1807.graph sourceMap2257=true := by decide +kernel
theorem fusedMap2257_checked : acceptsGraphIso
    (fused (graph core2257) (root 10) 0 0) DegreeOneSmallSpectrum1461.graph fusedMap2257=true := by decide +kernel
theorem certified2257 : Certified (graph core2257) (root 10) 0 0 :=
  of_native_maps core2257 DegreeOneSmallSpectrum1807.graph DegreeOneSmallSpectrum1461.graph
    sourceMap2257 fusedMap2257 sourceMap2257_checked fusedMap2257_checked
    DegreeOneSmallComparisons.comparison2257
#print axioms sourceMap2257_checked
#print axioms fusedMap2257_checked
#print axioms certified2257
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
