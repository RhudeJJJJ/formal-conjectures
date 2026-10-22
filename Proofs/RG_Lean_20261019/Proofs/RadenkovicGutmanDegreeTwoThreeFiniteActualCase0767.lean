/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0767 : Family 10 := level10.get ⟨1132,by decide⟩
def sourceMap0767 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0767 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0767_checked : acceptsGraphIso
    (source (graph core0767) (root 10) 0 0) DegreeOneSmallSpectrum1790.graph sourceMap0767=true := by decide +kernel
theorem fusedMap0767_checked : acceptsGraphIso
    (fused (graph core0767) (root 10) 0 0) DegreeOneSmallSpectrum1788.graph fusedMap0767=true := by decide +kernel
theorem certified0767 : Certified (graph core0767) (root 10) 0 0 :=
  of_native_maps core0767 DegreeOneSmallSpectrum1790.graph DegreeOneSmallSpectrum1788.graph
    sourceMap0767 fusedMap0767 sourceMap0767_checked fusedMap0767_checked
    DegreeTwoThreeFiniteComparisons.comparison0767
#print axioms sourceMap0767_checked
#print axioms fusedMap0767_checked
#print axioms certified0767
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
