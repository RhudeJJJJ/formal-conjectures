/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0733 : Family 10 := level10.get ⟨1047,by decide⟩
def sourceMap0733 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0733 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0733_checked : acceptsGraphIso
    (source (graph core0733) (root 10) 0 0) DegreeTwoThreeSpectrum1398.graph sourceMap0733=true := by decide +kernel
theorem fusedMap0733_checked : acceptsGraphIso
    (fused (graph core0733) (root 10) 0 0) DegreeOneSmallSpectrum1645.graph fusedMap0733=true := by decide +kernel
theorem certified0733 : Certified (graph core0733) (root 10) 0 0 :=
  of_native_maps core0733 DegreeTwoThreeSpectrum1398.graph DegreeOneSmallSpectrum1645.graph
    sourceMap0733 fusedMap0733 sourceMap0733_checked fusedMap0733_checked
    DegreeTwoThreeFiniteComparisons.comparison0733
#print axioms sourceMap0733_checked
#print axioms fusedMap0733_checked
#print axioms certified0733
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
