/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0038 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap0038 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0038 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0038_checked : acceptsGraphIso
    (source (graph core0038) (root 7) 0 0) DegreeTwoThreeSpectrum099.graph sourceMap0038=true := by decide +kernel
theorem fusedMap0038_checked : acceptsGraphIso
    (fused (graph core0038) (root 7) 0 0) DegreeOneSmallSpectrum141.graph fusedMap0038=true := by decide +kernel
theorem certified0038 : Certified (graph core0038) (root 7) 0 0 :=
  of_native_maps core0038 DegreeTwoThreeSpectrum099.graph DegreeOneSmallSpectrum141.graph
    sourceMap0038 fusedMap0038 sourceMap0038_checked fusedMap0038_checked
    DegreeTwoThreeFiniteComparisons.comparison0038
#print axioms sourceMap0038_checked
#print axioms fusedMap0038_checked
#print axioms certified0038
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
