/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2289 : Family 10 := level10.get ⟨901,by decide⟩
def sourceMap2289 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2289 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2289_checked : acceptsGraphIso
    (source (graph core2289) (root 10) 0 0) DegreeOneSmallSpectrum1711.graph sourceMap2289=true := by decide +kernel
theorem fusedMap2289_checked : acceptsGraphIso
    (fused (graph core2289) (root 10) 0 0) DegreeOneSmallSpectrum1470.graph fusedMap2289=true := by decide +kernel
theorem certified2289 : Certified (graph core2289) (root 10) 0 0 :=
  of_native_maps core2289 DegreeOneSmallSpectrum1711.graph DegreeOneSmallSpectrum1470.graph
    sourceMap2289 fusedMap2289 sourceMap2289_checked fusedMap2289_checked
    DegreeOneSmallComparisons.comparison2289
#print axioms sourceMap2289_checked
#print axioms fusedMap2289_checked
#print axioms certified2289
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
