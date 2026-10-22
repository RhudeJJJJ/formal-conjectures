/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0237 : Family 9 := level9.get ⟨273,by decide⟩
def sourceMap0237 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0237 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0237_checked : acceptsGraphIso
    (source (graph core0237) (root 9) 0 0) DegreeOneSmallSpectrum532.graph sourceMap0237=true := by decide +kernel
theorem fusedMap0237_checked : acceptsGraphIso
    (fused (graph core0237) (root 9) 0 0) DegreeOneSmallSpectrum516.graph fusedMap0237=true := by decide +kernel
theorem certified0237 : Certified (graph core0237) (root 9) 0 0 :=
  of_native_maps core0237 DegreeOneSmallSpectrum532.graph DegreeOneSmallSpectrum516.graph
    sourceMap0237 fusedMap0237 sourceMap0237_checked fusedMap0237_checked
    DegreeTwoThreeFiniteComparisons.comparison0237
#print axioms sourceMap0237_checked
#print axioms fusedMap0237_checked
#print axioms certified0237
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
