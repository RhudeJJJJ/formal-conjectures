/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0653 : Family 10 := level10.get ⟨842,by decide⟩
def sourceMap0653 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0653 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0653_checked : acceptsGraphIso
    (source (graph core0653) (root 10) 0 0) DegreeOneSmallSpectrum1692.graph sourceMap0653=true := by decide +kernel
theorem fusedMap0653_checked : acceptsGraphIso
    (fused (graph core0653) (root 10) 0 0) DegreeOneSmallSpectrum1440.graph fusedMap0653=true := by decide +kernel
theorem certified0653 : Certified (graph core0653) (root 10) 0 0 :=
  of_native_maps core0653 DegreeOneSmallSpectrum1692.graph DegreeOneSmallSpectrum1440.graph
    sourceMap0653 fusedMap0653 sourceMap0653_checked fusedMap0653_checked
    DegreeTwoThreeFiniteComparisons.comparison0653
#print axioms sourceMap0653_checked
#print axioms fusedMap0653_checked
#print axioms certified0653
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
