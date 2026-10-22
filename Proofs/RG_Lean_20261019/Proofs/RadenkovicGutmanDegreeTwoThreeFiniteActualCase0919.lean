/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0919 : Family 10 := level10.get ⟨1494,by decide⟩
def sourceMap0919 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0919 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0919_checked : acceptsGraphIso
    (source (graph core0919) (root 10) 0 0) DegreeOneSmallSpectrum994.graph sourceMap0919=true := by decide +kernel
theorem fusedMap0919_checked : acceptsGraphIso
    (fused (graph core0919) (root 10) 0 0) DegreeOneSmallSpectrum993.graph fusedMap0919=true := by decide +kernel
theorem certified0919 : Certified (graph core0919) (root 10) 0 0 :=
  of_native_maps core0919 DegreeOneSmallSpectrum994.graph DegreeOneSmallSpectrum993.graph
    sourceMap0919 fusedMap0919 sourceMap0919_checked fusedMap0919_checked
    DegreeTwoThreeFiniteComparisons.comparison0919
#print axioms sourceMap0919_checked
#print axioms fusedMap0919_checked
#print axioms certified0919
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
