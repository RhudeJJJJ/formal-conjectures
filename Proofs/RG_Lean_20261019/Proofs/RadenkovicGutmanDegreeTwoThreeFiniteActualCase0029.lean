/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0029 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap0029 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0029 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0029_checked : acceptsGraphIso
    (source (graph core0029) (root 7) 0 0) DegreeOneSmallSpectrum105.graph sourceMap0029=true := by decide +kernel
theorem fusedMap0029_checked : acceptsGraphIso
    (fused (graph core0029) (root 7) 0 0) DegreeOneSmallSpectrum084.graph fusedMap0029=true := by decide +kernel
theorem certified0029 : Certified (graph core0029) (root 7) 0 0 :=
  of_native_maps core0029 DegreeOneSmallSpectrum105.graph DegreeOneSmallSpectrum084.graph
    sourceMap0029 fusedMap0029 sourceMap0029_checked fusedMap0029_checked
    DegreeTwoThreeFiniteComparisons.comparison0029
#print axioms sourceMap0029_checked
#print axioms fusedMap0029_checked
#print axioms certified0029
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
