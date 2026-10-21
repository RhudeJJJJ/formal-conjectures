/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2317 : Family 10 := level10.get ⟨1008,by decide⟩
def sourceMap2317 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2317 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2317_checked : acceptsGraphIso
    (source (graph core2317) (root 10) 0 0) DegreeOneSmallSpectrum1556.graph sourceMap2317=true := by decide +kernel
theorem fusedMap2317_checked : acceptsGraphIso
    (fused (graph core2317) (root 10) 0 0) DegreeOneSmallSpectrum1558.graph fusedMap2317=true := by decide +kernel
theorem certified2317 : Certified (graph core2317) (root 10) 0 0 :=
  of_native_maps core2317 DegreeOneSmallSpectrum1556.graph DegreeOneSmallSpectrum1558.graph
    sourceMap2317 fusedMap2317 sourceMap2317_checked fusedMap2317_checked
    DegreeOneSmallComparisons.comparison2317
#print axioms sourceMap2317_checked
#print axioms fusedMap2317_checked
#print axioms certified2317
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
