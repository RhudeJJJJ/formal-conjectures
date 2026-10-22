/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0060 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap0060 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap0060 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (fusedLabel 7 0 0 v)
theorem sourceMap0060_checked : acceptsGraphIso
    (source (graph core0060) (root 7) 0 0) DegreeOneSmallSpectrum098.graph sourceMap0060=true := by decide +kernel
theorem fusedMap0060_checked : acceptsGraphIso
    (fused (graph core0060) (root 7) 0 0) DegreeOneSmallSpectrum097.graph fusedMap0060=true := by decide +kernel
theorem certified0060 : Certified (graph core0060) (root 7) 0 0 :=
  of_native_maps core0060 DegreeOneSmallSpectrum098.graph DegreeOneSmallSpectrum097.graph
    sourceMap0060 fusedMap0060 sourceMap0060_checked fusedMap0060_checked
    DegreeTwoThreeFiniteComparisons.comparison0060
#print axioms sourceMap0060_checked
#print axioms fusedMap0060_checked
#print axioms certified0060
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
