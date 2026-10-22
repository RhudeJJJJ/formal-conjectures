/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0177 : Family 9 := level9.get ⟨87,by decide⟩
def sourceMap0177 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0177 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0177_checked : acceptsGraphIso
    (source (graph core0177) (root 9) 0 0) DegreeOneSmallSpectrum415.graph sourceMap0177=true := by decide +kernel
theorem fusedMap0177_checked : acceptsGraphIso
    (fused (graph core0177) (root 9) 0 0) DegreeOneSmallSpectrum551.graph fusedMap0177=true := by decide +kernel
theorem certified0177 : Certified (graph core0177) (root 9) 0 0 :=
  of_native_maps core0177 DegreeOneSmallSpectrum415.graph DegreeOneSmallSpectrum551.graph
    sourceMap0177 fusedMap0177 sourceMap0177_checked fusedMap0177_checked
    DegreeTwoThreeFiniteComparisons.comparison0177
#print axioms sourceMap0177_checked
#print axioms fusedMap0177_checked
#print axioms certified0177
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
