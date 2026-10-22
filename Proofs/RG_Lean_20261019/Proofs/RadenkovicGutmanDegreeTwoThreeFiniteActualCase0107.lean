/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0107 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap0107 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0107 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0107_checked : acceptsGraphIso
    (source (graph core0107) (root 8) 0 0) DegreeTwoThreeSpectrum233.graph sourceMap0107=true := by decide +kernel
theorem fusedMap0107_checked : acceptsGraphIso
    (fused (graph core0107) (root 8) 0 0) DegreeOneSmallSpectrum336.graph fusedMap0107=true := by decide +kernel
theorem certified0107 : Certified (graph core0107) (root 8) 0 0 :=
  of_native_maps core0107 DegreeTwoThreeSpectrum233.graph DegreeOneSmallSpectrum336.graph
    sourceMap0107 fusedMap0107 sourceMap0107_checked fusedMap0107_checked
    DegreeTwoThreeFiniteComparisons.comparison0107
#print axioms sourceMap0107_checked
#print axioms fusedMap0107_checked
#print axioms certified0107
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
