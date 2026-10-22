/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0350 : Family 9 := level9.get ⟨557,by decide⟩
def sourceMap0350 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0350 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0350_checked : acceptsGraphIso
    (source (graph core0350) (root 9) 0 0) DegreeOneSmallSpectrum625.graph sourceMap0350=true := by decide +kernel
theorem fusedMap0350_checked : acceptsGraphIso
    (fused (graph core0350) (root 9) 0 0) DegreeOneSmallSpectrum624.graph fusedMap0350=true := by decide +kernel
theorem certified0350 : Certified (graph core0350) (root 9) 0 0 :=
  of_native_maps core0350 DegreeOneSmallSpectrum625.graph DegreeOneSmallSpectrum624.graph
    sourceMap0350 fusedMap0350 sourceMap0350_checked fusedMap0350_checked
    DegreeTwoThreeFiniteComparisons.comparison0350
#print axioms sourceMap0350_checked
#print axioms fusedMap0350_checked
#print axioms certified0350
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
