/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0289 : Family 9 := level9.get ⟨407,by decide⟩
def sourceMap0289 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0289 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0289_checked : acceptsGraphIso
    (source (graph core0289) (root 9) 0 0) DegreeOneSmallSpectrum466.graph sourceMap0289=true := by decide +kernel
theorem fusedMap0289_checked : acceptsGraphIso
    (fused (graph core0289) (root 9) 0 0) DegreeOneSmallSpectrum461.graph fusedMap0289=true := by decide +kernel
theorem certified0289 : Certified (graph core0289) (root 9) 0 0 :=
  of_native_maps core0289 DegreeOneSmallSpectrum466.graph DegreeOneSmallSpectrum461.graph
    sourceMap0289 fusedMap0289 sourceMap0289_checked fusedMap0289_checked
    DegreeTwoThreeFiniteComparisons.comparison0289
#print axioms sourceMap0289_checked
#print axioms fusedMap0289_checked
#print axioms certified0289
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
