/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0684 : Family 10 := level10.get ⟨918,by decide⟩
def sourceMap0684 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0684 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0684_checked : acceptsGraphIso
    (source (graph core0684) (root 10) 0 0) DegreeOneSmallSpectrum1423.graph sourceMap0684=true := by decide +kernel
theorem fusedMap0684_checked : acceptsGraphIso
    (fused (graph core0684) (root 10) 0 0) DegreeOneSmallSpectrum1413.graph fusedMap0684=true := by decide +kernel
theorem certified0684 : Certified (graph core0684) (root 10) 0 0 :=
  of_native_maps core0684 DegreeOneSmallSpectrum1423.graph DegreeOneSmallSpectrum1413.graph
    sourceMap0684 fusedMap0684 sourceMap0684_checked fusedMap0684_checked
    DegreeTwoThreeFiniteComparisons.comparison0684
#print axioms sourceMap0684_checked
#print axioms fusedMap0684_checked
#print axioms certified0684
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
