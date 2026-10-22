/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0685 : Family 10 := level10.get ⟨920,by decide⟩
def sourceMap0685 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0685 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0685_checked : acceptsGraphIso
    (source (graph core0685) (root 10) 0 0) DegreeOneSmallSpectrum1020.graph sourceMap0685=true := by decide +kernel
theorem fusedMap0685_checked : acceptsGraphIso
    (fused (graph core0685) (root 10) 0 0) DegreeOneSmallSpectrum1014.graph fusedMap0685=true := by decide +kernel
theorem certified0685 : Certified (graph core0685) (root 10) 0 0 :=
  of_native_maps core0685 DegreeOneSmallSpectrum1020.graph DegreeOneSmallSpectrum1014.graph
    sourceMap0685 fusedMap0685 sourceMap0685_checked fusedMap0685_checked
    DegreeTwoThreeFiniteComparisons.comparison0685
#print axioms sourceMap0685_checked
#print axioms fusedMap0685_checked
#print axioms certified0685
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
