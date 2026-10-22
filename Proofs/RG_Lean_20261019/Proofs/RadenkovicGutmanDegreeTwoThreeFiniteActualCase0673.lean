/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0673 : Family 10 := level10.get ⟨892,by decide⟩
def sourceMap0673 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0673 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0673_checked : acceptsGraphIso
    (source (graph core0673) (root 10) 0 0) DegreeOneSmallSpectrum1133.graph sourceMap0673=true := by decide +kernel
theorem fusedMap0673_checked : acceptsGraphIso
    (fused (graph core0673) (root 10) 0 0) DegreeOneSmallSpectrum1110.graph fusedMap0673=true := by decide +kernel
theorem certified0673 : Certified (graph core0673) (root 10) 0 0 :=
  of_native_maps core0673 DegreeOneSmallSpectrum1133.graph DegreeOneSmallSpectrum1110.graph
    sourceMap0673 fusedMap0673 sourceMap0673_checked fusedMap0673_checked
    DegreeTwoThreeFiniteComparisons.comparison0673
#print axioms sourceMap0673_checked
#print axioms fusedMap0673_checked
#print axioms certified0673
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
