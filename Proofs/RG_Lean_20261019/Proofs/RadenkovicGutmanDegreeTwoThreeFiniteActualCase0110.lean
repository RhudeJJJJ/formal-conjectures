/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0110 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap0110 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0110 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0110_checked : acceptsGraphIso
    (source (graph core0110) (root 8) 0 0) DegreeOneSmallSpectrum252.graph sourceMap0110=true := by decide +kernel
theorem fusedMap0110_checked : acceptsGraphIso
    (fused (graph core0110) (root 8) 0 0) DegreeOneSmallSpectrum340.graph fusedMap0110=true := by decide +kernel
theorem certified0110 : Certified (graph core0110) (root 8) 0 0 :=
  of_native_maps core0110 DegreeOneSmallSpectrum252.graph DegreeOneSmallSpectrum340.graph
    sourceMap0110 fusedMap0110 sourceMap0110_checked fusedMap0110_checked
    DegreeTwoThreeFiniteComparisons.comparison0110
#print axioms sourceMap0110_checked
#print axioms fusedMap0110_checked
#print axioms certified0110
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
