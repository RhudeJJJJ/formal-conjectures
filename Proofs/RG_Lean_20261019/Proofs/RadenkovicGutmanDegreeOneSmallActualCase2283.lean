/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2283 : Family 10 := level10.get ⟨887,by decide⟩
def sourceMap2283 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2283 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2283_checked : acceptsGraphIso
    (source (graph core2283) (root 10) 0 0) DegreeOneSmallSpectrum1793.graph sourceMap2283=true := by decide +kernel
theorem fusedMap2283_checked : acceptsGraphIso
    (fused (graph core2283) (root 10) 0 0) DegreeOneSmallSpectrum1495.graph fusedMap2283=true := by decide +kernel
theorem certified2283 : Certified (graph core2283) (root 10) 0 0 :=
  of_native_maps core2283 DegreeOneSmallSpectrum1793.graph DegreeOneSmallSpectrum1495.graph
    sourceMap2283 fusedMap2283 sourceMap2283_checked fusedMap2283_checked
    DegreeOneSmallComparisons.comparison2283
#print axioms sourceMap2283_checked
#print axioms fusedMap2283_checked
#print axioms certified2283
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
