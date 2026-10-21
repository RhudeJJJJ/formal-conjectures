/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2140 : Family 10 := level10.get ⟨586,by decide⟩
def sourceMap2140 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2140 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2140_checked : acceptsGraphIso
    (source (graph core2140) (root 10) 0 0) DegreeOneSmallSpectrum1794.graph sourceMap2140=true := by decide +kernel
theorem fusedMap2140_checked : acceptsGraphIso
    (fused (graph core2140) (root 10) 0 0) DegreeOneSmallSpectrum1133.graph fusedMap2140=true := by decide +kernel
theorem certified2140 : Certified (graph core2140) (root 10) 0 0 :=
  of_native_maps core2140 DegreeOneSmallSpectrum1794.graph DegreeOneSmallSpectrum1133.graph
    sourceMap2140 fusedMap2140 sourceMap2140_checked fusedMap2140_checked
    DegreeOneSmallComparisons.comparison2140
#print axioms sourceMap2140_checked
#print axioms fusedMap2140_checked
#print axioms certified2140
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
