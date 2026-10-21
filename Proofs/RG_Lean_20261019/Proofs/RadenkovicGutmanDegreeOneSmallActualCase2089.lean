/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2089 : Family 10 := level10.get ⟨503,by decide⟩
def sourceMap2089 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2089 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2089_checked : acceptsGraphIso
    (source (graph core2089) (root 10) 0 0) DegreeOneSmallSpectrum1574.graph sourceMap2089=true := by decide +kernel
theorem fusedMap2089_checked : acceptsGraphIso
    (fused (graph core2089) (root 10) 0 0) DegreeOneSmallSpectrum987.graph fusedMap2089=true := by decide +kernel
theorem certified2089 : Certified (graph core2089) (root 10) 0 0 :=
  of_native_maps core2089 DegreeOneSmallSpectrum1574.graph DegreeOneSmallSpectrum987.graph
    sourceMap2089 fusedMap2089 sourceMap2089_checked fusedMap2089_checked
    DegreeOneSmallComparisons.comparison2089
#print axioms sourceMap2089_checked
#print axioms fusedMap2089_checked
#print axioms certified2089
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
