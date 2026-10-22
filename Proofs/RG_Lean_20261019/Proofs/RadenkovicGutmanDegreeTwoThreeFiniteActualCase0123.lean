/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0123 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap0123 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0123 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0123_checked : acceptsGraphIso
    (source (graph core0123) (root 8) 0 0) DegreeOneSmallSpectrum184.graph sourceMap0123=true := by decide +kernel
theorem fusedMap0123_checked : acceptsGraphIso
    (fused (graph core0123) (root 8) 0 0) DegreeOneSmallSpectrum183.graph fusedMap0123=true := by decide +kernel
theorem certified0123 : Certified (graph core0123) (root 8) 0 0 :=
  of_native_maps core0123 DegreeOneSmallSpectrum184.graph DegreeOneSmallSpectrum183.graph
    sourceMap0123 fusedMap0123 sourceMap0123_checked fusedMap0123_checked
    DegreeTwoThreeFiniteComparisons.comparison0123
#print axioms sourceMap0123_checked
#print axioms fusedMap0123_checked
#print axioms certified0123
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
