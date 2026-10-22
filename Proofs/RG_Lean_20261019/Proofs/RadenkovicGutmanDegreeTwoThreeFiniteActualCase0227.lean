/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0227 : Family 9 := level9.get ⟨245,by decide⟩
def sourceMap0227 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0227 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0227_checked : acceptsGraphIso
    (source (graph core0227) (root 9) 0 0) DegreeOneSmallSpectrum526.graph sourceMap0227=true := by decide +kernel
theorem fusedMap0227_checked : acceptsGraphIso
    (fused (graph core0227) (root 9) 0 0) DegreeOneSmallSpectrum508.graph fusedMap0227=true := by decide +kernel
theorem certified0227 : Certified (graph core0227) (root 9) 0 0 :=
  of_native_maps core0227 DegreeOneSmallSpectrum526.graph DegreeOneSmallSpectrum508.graph
    sourceMap0227 fusedMap0227 sourceMap0227_checked fusedMap0227_checked
    DegreeTwoThreeFiniteComparisons.comparison0227
#print axioms sourceMap0227_checked
#print axioms fusedMap0227_checked
#print axioms certified0227
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
