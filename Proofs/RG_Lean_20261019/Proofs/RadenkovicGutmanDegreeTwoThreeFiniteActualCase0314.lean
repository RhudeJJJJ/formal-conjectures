/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0314 : Family 9 := level9.get ⟨471,by decide⟩
def sourceMap0314 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0314 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0314_checked : acceptsGraphIso
    (source (graph core0314) (root 9) 0 0) DegreeOneSmallSpectrum807.graph sourceMap0314=true := by decide +kernel
theorem fusedMap0314_checked : acceptsGraphIso
    (fused (graph core0314) (root 9) 0 0) DegreeOneSmallSpectrum793.graph fusedMap0314=true := by decide +kernel
theorem certified0314 : Certified (graph core0314) (root 9) 0 0 :=
  of_native_maps core0314 DegreeOneSmallSpectrum807.graph DegreeOneSmallSpectrum793.graph
    sourceMap0314 fusedMap0314 sourceMap0314_checked fusedMap0314_checked
    DegreeTwoThreeFiniteComparisons.comparison0314
#print axioms sourceMap0314_checked
#print axioms fusedMap0314_checked
#print axioms certified0314
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
