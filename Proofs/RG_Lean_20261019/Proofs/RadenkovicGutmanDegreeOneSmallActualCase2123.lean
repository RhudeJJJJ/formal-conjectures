/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2123 : Family 10 := level10.get ⟨561,by decide⟩
def sourceMap2123 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2123 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2123_checked : acceptsGraphIso
    (source (graph core2123) (root 10) 0 0) DegreeOneSmallSpectrum1714.graph sourceMap2123=true := by decide +kernel
theorem fusedMap2123_checked : acceptsGraphIso
    (fused (graph core2123) (root 10) 0 0) DegreeOneSmallSpectrum1087.graph fusedMap2123=true := by decide +kernel
theorem certified2123 : Certified (graph core2123) (root 10) 0 0 :=
  of_native_maps core2123 DegreeOneSmallSpectrum1714.graph DegreeOneSmallSpectrum1087.graph
    sourceMap2123 fusedMap2123 sourceMap2123_checked fusedMap2123_checked
    DegreeOneSmallComparisons.comparison2123
#print axioms sourceMap2123_checked
#print axioms fusedMap2123_checked
#print axioms certified2123
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
