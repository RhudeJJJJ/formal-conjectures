/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2121 : Family 10 := level10.get ⟨559,by decide⟩
def sourceMap2121 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2121 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2121_checked : acceptsGraphIso
    (source (graph core2121) (root 10) 0 0) DegreeOneSmallSpectrum1707.graph sourceMap2121=true := by decide +kernel
theorem fusedMap2121_checked : acceptsGraphIso
    (fused (graph core2121) (root 10) 0 0) DegreeOneSmallSpectrum1083.graph fusedMap2121=true := by decide +kernel
theorem certified2121 : Certified (graph core2121) (root 10) 0 0 :=
  of_native_maps core2121 DegreeOneSmallSpectrum1707.graph DegreeOneSmallSpectrum1083.graph
    sourceMap2121 fusedMap2121 sourceMap2121_checked fusedMap2121_checked
    DegreeOneSmallComparisons.comparison2121
#print axioms sourceMap2121_checked
#print axioms fusedMap2121_checked
#print axioms certified2121
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
