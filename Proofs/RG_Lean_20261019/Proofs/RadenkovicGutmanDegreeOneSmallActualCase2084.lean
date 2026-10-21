/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2084 : Family 10 := level10.get ⟨497,by decide⟩
def sourceMap2084 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2084 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2084_checked : acceptsGraphIso
    (source (graph core2084) (root 10) 0 0) DegreeOneSmallSpectrum1528.graph sourceMap2084=true := by decide +kernel
theorem fusedMap2084_checked : acceptsGraphIso
    (fused (graph core2084) (root 10) 0 0) DegreeOneSmallSpectrum979.graph fusedMap2084=true := by decide +kernel
theorem certified2084 : Certified (graph core2084) (root 10) 0 0 :=
  of_native_maps core2084 DegreeOneSmallSpectrum1528.graph DegreeOneSmallSpectrum979.graph
    sourceMap2084 fusedMap2084 sourceMap2084_checked fusedMap2084_checked
    DegreeOneSmallComparisons.comparison2084
#print axioms sourceMap2084_checked
#print axioms fusedMap2084_checked
#print axioms certified2084
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
