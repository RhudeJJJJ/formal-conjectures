/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2080 : Family 10 := level10.get ⟨473,by decide⟩
def sourceMap2080 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2080 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2080_checked : acceptsGraphIso
    (source (graph core2080) (root 10) 0 0) DegreeOneSmallSpectrum1083.graph sourceMap2080=true := by decide +kernel
theorem fusedMap2080_checked : acceptsGraphIso
    (fused (graph core2080) (root 10) 0 0) DegreeOneSmallSpectrum1471.graph fusedMap2080=true := by decide +kernel
theorem certified2080 : Certified (graph core2080) (root 10) 0 0 :=
  of_native_maps core2080 DegreeOneSmallSpectrum1083.graph DegreeOneSmallSpectrum1471.graph
    sourceMap2080 fusedMap2080 sourceMap2080_checked fusedMap2080_checked
    DegreeOneSmallComparisons.comparison2080
#print axioms sourceMap2080_checked
#print axioms fusedMap2080_checked
#print axioms certified2080
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
