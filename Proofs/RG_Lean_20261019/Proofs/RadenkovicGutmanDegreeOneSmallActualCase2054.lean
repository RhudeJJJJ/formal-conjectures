/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2054 : Family 10 := level10.get ⟨428,by decide⟩
def sourceMap2054 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2054 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2054_checked : acceptsGraphIso
    (source (graph core2054) (root 10) 0 0) DegreeOneSmallSpectrum1509.graph sourceMap2054=true := by decide +kernel
theorem fusedMap2054_checked : acceptsGraphIso
    (fused (graph core2054) (root 10) 0 0) DegreeOneSmallSpectrum1508.graph fusedMap2054=true := by decide +kernel
theorem certified2054 : Certified (graph core2054) (root 10) 0 0 :=
  of_native_maps core2054 DegreeOneSmallSpectrum1509.graph DegreeOneSmallSpectrum1508.graph
    sourceMap2054 fusedMap2054 sourceMap2054_checked fusedMap2054_checked
    DegreeOneSmallComparisons.comparison2054
#print axioms sourceMap2054_checked
#print axioms fusedMap2054_checked
#print axioms certified2054
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
