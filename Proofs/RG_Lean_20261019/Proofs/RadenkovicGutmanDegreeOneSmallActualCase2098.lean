/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2098 : Family 10 := level10.get ⟨517,by decide⟩
def sourceMap2098 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2098 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2098_checked : acceptsGraphIso
    (source (graph core2098) (root 10) 0 0) DegreeOneSmallSpectrum1626.graph sourceMap2098=true := by decide +kernel
theorem fusedMap2098_checked : acceptsGraphIso
    (fused (graph core2098) (root 10) 0 0) DegreeOneSmallSpectrum1010.graph fusedMap2098=true := by decide +kernel
theorem certified2098 : Certified (graph core2098) (root 10) 0 0 :=
  of_native_maps core2098 DegreeOneSmallSpectrum1626.graph DegreeOneSmallSpectrum1010.graph
    sourceMap2098 fusedMap2098 sourceMap2098_checked fusedMap2098_checked
    DegreeOneSmallComparisons.comparison2098
#print axioms sourceMap2098_checked
#print axioms fusedMap2098_checked
#print axioms certified2098
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
