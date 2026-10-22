/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0260 : Family 9 := level9.get ⟨336,by decide⟩
def sourceMap0260 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0260 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0260_checked : acceptsGraphIso
    (source (graph core0260) (root 9) 0 0) DegreeTwoThreeSpectrum555.graph sourceMap0260=true := by decide +kernel
theorem fusedMap0260_checked : acceptsGraphIso
    (fused (graph core0260) (root 9) 0 0) DegreeOneSmallSpectrum648.graph fusedMap0260=true := by decide +kernel
theorem certified0260 : Certified (graph core0260) (root 9) 0 0 :=
  of_native_maps core0260 DegreeTwoThreeSpectrum555.graph DegreeOneSmallSpectrum648.graph
    sourceMap0260 fusedMap0260 sourceMap0260_checked fusedMap0260_checked
    DegreeTwoThreeFiniteComparisons.comparison0260
#print axioms sourceMap0260_checked
#print axioms fusedMap0260_checked
#print axioms certified0260
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
