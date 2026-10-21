/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2083 : Family 10 := level10.get ⟨480,by decide⟩
def sourceMap2083 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2083 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2083_checked : acceptsGraphIso
    (source (graph core2083) (root 10) 0 0) DegreeOneSmallSpectrum1113.graph sourceMap2083=true := by decide +kernel
theorem fusedMap2083_checked : acceptsGraphIso
    (fused (graph core2083) (root 10) 0 0) DegreeOneSmallSpectrum1494.graph fusedMap2083=true := by decide +kernel
theorem certified2083 : Certified (graph core2083) (root 10) 0 0 :=
  of_native_maps core2083 DegreeOneSmallSpectrum1113.graph DegreeOneSmallSpectrum1494.graph
    sourceMap2083 fusedMap2083 sourceMap2083_checked fusedMap2083_checked
    DegreeOneSmallComparisons.comparison2083
#print axioms sourceMap2083_checked
#print axioms fusedMap2083_checked
#print axioms certified2083
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
