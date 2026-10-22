/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0315 : Family 9 := level9.get ⟨473,by decide⟩
def sourceMap0315 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0315 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0315_checked : acceptsGraphIso
    (source (graph core0315) (root 9) 0 0) DegreeOneSmallSpectrum548.graph sourceMap0315=true := by decide +kernel
theorem fusedMap0315_checked : acceptsGraphIso
    (fused (graph core0315) (root 9) 0 0) DegreeOneSmallSpectrum547.graph fusedMap0315=true := by decide +kernel
theorem certified0315 : Certified (graph core0315) (root 9) 0 0 :=
  of_native_maps core0315 DegreeOneSmallSpectrum548.graph DegreeOneSmallSpectrum547.graph
    sourceMap0315 fusedMap0315 sourceMap0315_checked fusedMap0315_checked
    DegreeTwoThreeFiniteComparisons.comparison0315
#print axioms sourceMap0315_checked
#print axioms fusedMap0315_checked
#print axioms certified0315
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
