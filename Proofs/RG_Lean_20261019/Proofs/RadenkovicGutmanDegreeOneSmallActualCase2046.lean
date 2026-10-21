/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2046 : Family 10 := level10.get ⟨408,by decide⟩
def sourceMap2046 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2046 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2046_checked : acceptsGraphIso
    (source (graph core2046) (root 10) 0 0) DegreeOneSmallSpectrum1215.graph sourceMap2046=true := by decide +kernel
theorem fusedMap2046_checked : acceptsGraphIso
    (fused (graph core2046) (root 10) 0 0) DegreeOneSmallSpectrum1507.graph fusedMap2046=true := by decide +kernel
theorem certified2046 : Certified (graph core2046) (root 10) 0 0 :=
  of_native_maps core2046 DegreeOneSmallSpectrum1215.graph DegreeOneSmallSpectrum1507.graph
    sourceMap2046 fusedMap2046 sourceMap2046_checked fusedMap2046_checked
    DegreeOneSmallComparisons.comparison2046
#print axioms sourceMap2046_checked
#print axioms fusedMap2046_checked
#print axioms certified2046
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
