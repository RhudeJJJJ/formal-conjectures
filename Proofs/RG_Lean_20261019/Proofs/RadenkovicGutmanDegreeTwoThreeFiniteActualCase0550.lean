/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0550 : Family 10 := level10.get ⟨550,by decide⟩
def sourceMap0550 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0550 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0550_checked : acceptsGraphIso
    (source (graph core0550) (root 10) 0 0) DegreeTwoThreeSpectrum1382.graph sourceMap0550=true := by decide +kernel
theorem fusedMap0550_checked : acceptsGraphIso
    (fused (graph core0550) (root 10) 0 0) DegreeOneSmallSpectrum1070.graph fusedMap0550=true := by decide +kernel
theorem certified0550 : Certified (graph core0550) (root 10) 0 0 :=
  of_native_maps core0550 DegreeTwoThreeSpectrum1382.graph DegreeOneSmallSpectrum1070.graph
    sourceMap0550 fusedMap0550 sourceMap0550_checked fusedMap0550_checked
    DegreeTwoThreeFiniteComparisons.comparison0550
#print axioms sourceMap0550_checked
#print axioms fusedMap0550_checked
#print axioms certified0550
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
