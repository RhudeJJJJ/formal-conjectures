/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0044 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap0044 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0044 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap0044_checked : acceptsGraphIso
    (source (graph core0044) (root 7) 0 0) DegreeOneSmallSpectrum088.graph sourceMap0044=true := by decide +kernel
theorem fusedMap0044_checked : acceptsGraphIso
    (fused (graph core0044) (root 7) 0 0) DegreeOneSmallSpectrum087.graph fusedMap0044=true := by decide +kernel
theorem certified0044 : Certified (graph core0044) (root 7) 0 0 :=
  of_native_maps core0044 DegreeOneSmallSpectrum088.graph DegreeOneSmallSpectrum087.graph
    sourceMap0044 fusedMap0044 sourceMap0044_checked fusedMap0044_checked
    DegreeTwoThreeFiniteComparisons.comparison0044
#print axioms sourceMap0044_checked
#print axioms fusedMap0044_checked
#print axioms certified0044
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
