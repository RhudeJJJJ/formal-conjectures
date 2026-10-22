/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0101 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap0101 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0101 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0101_checked : acceptsGraphIso
    (source (graph core0101) (root 8) 0 0) DegreeOneSmallSpectrum195.graph sourceMap0101=true := by decide +kernel
theorem fusedMap0101_checked : acceptsGraphIso
    (fused (graph core0101) (root 8) 0 0) DegreeOneSmallSpectrum194.graph fusedMap0101=true := by decide +kernel
theorem certified0101 : Certified (graph core0101) (root 8) 0 0 :=
  of_native_maps core0101 DegreeOneSmallSpectrum195.graph DegreeOneSmallSpectrum194.graph
    sourceMap0101 fusedMap0101 sourceMap0101_checked fusedMap0101_checked
    DegreeTwoThreeFiniteComparisons.comparison0101
#print axioms sourceMap0101_checked
#print axioms fusedMap0101_checked
#print axioms certified0101
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
