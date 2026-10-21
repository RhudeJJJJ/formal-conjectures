/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2261 : Family 10 := level10.get ⟨843,by decide⟩
def sourceMap2261 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2261 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2261_checked : acceptsGraphIso
    (source (graph core2261) (root 10) 0 0) DegreeOneSmallSpectrum1880.graph sourceMap2261=true := by decide +kernel
theorem fusedMap2261_checked : acceptsGraphIso
    (fused (graph core2261) (root 10) 0 0) DegreeOneSmallSpectrum1468.graph fusedMap2261=true := by decide +kernel
theorem certified2261 : Certified (graph core2261) (root 10) 0 0 :=
  of_native_maps core2261 DegreeOneSmallSpectrum1880.graph DegreeOneSmallSpectrum1468.graph
    sourceMap2261 fusedMap2261 sourceMap2261_checked fusedMap2261_checked
    DegreeOneSmallComparisons.comparison2261
#print axioms sourceMap2261_checked
#print axioms fusedMap2261_checked
#print axioms certified2261
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
