/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2298 : Family 10 := level10.get ⟨932,by decide⟩
def sourceMap2298 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2298 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2298_checked : acceptsGraphIso
    (source (graph core2298) (root 10) 0 0) DegreeOneSmallSpectrum1366.graph sourceMap2298=true := by decide +kernel
theorem fusedMap2298_checked : acceptsGraphIso
    (fused (graph core2298) (root 10) 0 0) DegreeOneSmallSpectrum1365.graph fusedMap2298=true := by decide +kernel
theorem certified2298 : Certified (graph core2298) (root 10) 0 0 :=
  of_native_maps core2298 DegreeOneSmallSpectrum1366.graph DegreeOneSmallSpectrum1365.graph
    sourceMap2298 fusedMap2298 sourceMap2298_checked fusedMap2298_checked
    DegreeOneSmallComparisons.comparison2298
#print axioms sourceMap2298_checked
#print axioms fusedMap2298_checked
#print axioms certified2298
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
