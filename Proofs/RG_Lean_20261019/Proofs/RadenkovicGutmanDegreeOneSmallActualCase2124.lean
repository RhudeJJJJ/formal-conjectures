/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2124 : Family 10 := level10.get ⟨563,by decide⟩
def sourceMap2124 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2124 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2124_checked : acceptsGraphIso
    (source (graph core2124) (root 10) 0 0) DegreeOneSmallSpectrum1729.graph sourceMap2124=true := by decide +kernel
theorem fusedMap2124_checked : acceptsGraphIso
    (fused (graph core2124) (root 10) 0 0) DegreeOneSmallSpectrum1089.graph fusedMap2124=true := by decide +kernel
theorem certified2124 : Certified (graph core2124) (root 10) 0 0 :=
  of_native_maps core2124 DegreeOneSmallSpectrum1729.graph DegreeOneSmallSpectrum1089.graph
    sourceMap2124 fusedMap2124 sourceMap2124_checked fusedMap2124_checked
    DegreeOneSmallComparisons.comparison2124
#print axioms sourceMap2124_checked
#print axioms fusedMap2124_checked
#print axioms certified2124
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
