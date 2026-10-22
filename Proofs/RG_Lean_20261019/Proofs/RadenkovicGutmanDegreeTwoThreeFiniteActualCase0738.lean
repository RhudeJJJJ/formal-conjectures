/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0738 : Family 10 := level10.get ⟨1059,by decide⟩
def sourceMap0738 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0738 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0738_checked : acceptsGraphIso
    (source (graph core0738) (root 10) 0 0) DegreeTwoThreeSpectrum1434.graph sourceMap0738=true := by decide +kernel
theorem fusedMap0738_checked : acceptsGraphIso
    (fused (graph core0738) (root 10) 0 0) DegreeOneSmallSpectrum1663.graph fusedMap0738=true := by decide +kernel
theorem certified0738 : Certified (graph core0738) (root 10) 0 0 :=
  of_native_maps core0738 DegreeTwoThreeSpectrum1434.graph DegreeOneSmallSpectrum1663.graph
    sourceMap0738 fusedMap0738 sourceMap0738_checked fusedMap0738_checked
    DegreeTwoThreeFiniteComparisons.comparison0738
#print axioms sourceMap0738_checked
#print axioms fusedMap0738_checked
#print axioms certified0738
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
