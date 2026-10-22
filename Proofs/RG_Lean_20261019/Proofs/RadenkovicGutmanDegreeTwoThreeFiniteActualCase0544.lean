/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0544 : Family 10 := level10.get ⟨531,by decide⟩
def sourceMap0544 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0544 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0544_checked : acceptsGraphIso
    (source (graph core0544) (root 10) 0 0) DegreeTwoThreeSpectrum1418.graph sourceMap0544=true := by decide +kernel
theorem fusedMap0544_checked : acceptsGraphIso
    (fused (graph core0544) (root 10) 0 0) DegreeOneSmallSpectrum1032.graph fusedMap0544=true := by decide +kernel
theorem certified0544 : Certified (graph core0544) (root 10) 0 0 :=
  of_native_maps core0544 DegreeTwoThreeSpectrum1418.graph DegreeOneSmallSpectrum1032.graph
    sourceMap0544 fusedMap0544 sourceMap0544_checked fusedMap0544_checked
    DegreeTwoThreeFiniteComparisons.comparison0544
#print axioms sourceMap0544_checked
#print axioms fusedMap0544_checked
#print axioms certified0544
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
