/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0496 : Family 10 := level10.get ⟨387,by decide⟩
def sourceMap0496 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0496 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0496_checked : acceptsGraphIso
    (source (graph core0496) (root 10) 0 0) DegreeOneSmallSpectrum1034.graph sourceMap0496=true := by decide +kernel
theorem fusedMap0496_checked : acceptsGraphIso
    (fused (graph core0496) (root 10) 0 0) DegreeOneSmallSpectrum1430.graph fusedMap0496=true := by decide +kernel
theorem certified0496 : Certified (graph core0496) (root 10) 0 0 :=
  of_native_maps core0496 DegreeOneSmallSpectrum1034.graph DegreeOneSmallSpectrum1430.graph
    sourceMap0496 fusedMap0496 sourceMap0496_checked fusedMap0496_checked
    DegreeTwoThreeFiniteComparisons.comparison0496
#print axioms sourceMap0496_checked
#print axioms fusedMap0496_checked
#print axioms certified0496
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
