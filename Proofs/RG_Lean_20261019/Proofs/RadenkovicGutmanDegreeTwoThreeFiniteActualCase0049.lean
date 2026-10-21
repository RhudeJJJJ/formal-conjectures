/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0049 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap0049 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0049 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0049_checked : acceptsGraphIso
    (source (graph core0049) (root 7) 0 0) DegreeOneSmallSpectrum156.graph sourceMap0049=true := by decide +kernel
theorem fusedMap0049_checked : acceptsGraphIso
    (fused (graph core0049) (root 7) 0 0) DegreeOneSmallSpectrum110.graph fusedMap0049=true := by decide +kernel
theorem certified0049 : Certified (graph core0049) (root 7) 0 0 :=
  of_native_maps core0049 DegreeOneSmallSpectrum156.graph DegreeOneSmallSpectrum110.graph
    sourceMap0049 fusedMap0049 sourceMap0049_checked fusedMap0049_checked
    DegreeTwoThreeFiniteComparisons.comparison0049
#print axioms sourceMap0049_checked
#print axioms fusedMap0049_checked
#print axioms certified0049
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
