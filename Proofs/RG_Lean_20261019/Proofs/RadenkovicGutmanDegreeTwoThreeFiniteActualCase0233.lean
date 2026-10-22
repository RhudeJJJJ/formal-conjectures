/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0233 : Family 9 := level9.get ⟨264,by decide⟩
def sourceMap0233 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0233 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0233_checked : acceptsGraphIso
    (source (graph core0233) (root 9) 0 0) DegreeOneSmallSpectrum656.graph sourceMap0233=true := by decide +kernel
theorem fusedMap0233_checked : acceptsGraphIso
    (fused (graph core0233) (root 9) 0 0) DegreeOneSmallSpectrum547.graph fusedMap0233=true := by decide +kernel
theorem certified0233 : Certified (graph core0233) (root 9) 0 0 :=
  of_native_maps core0233 DegreeOneSmallSpectrum656.graph DegreeOneSmallSpectrum547.graph
    sourceMap0233 fusedMap0233 sourceMap0233_checked fusedMap0233_checked
    DegreeTwoThreeFiniteComparisons.comparison0233
#print axioms sourceMap0233_checked
#print axioms fusedMap0233_checked
#print axioms certified0233
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
