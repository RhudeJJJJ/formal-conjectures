/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0901 : Family 10 := level10.get ⟨1449,by decide⟩
def sourceMap0901 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0901 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0901_checked : acceptsGraphIso
    (source (graph core0901) (root 10) 0 0) DegreeOneSmallSpectrum1491.graph sourceMap0901=true := by decide +kernel
theorem fusedMap0901_checked : acceptsGraphIso
    (fused (graph core0901) (root 10) 0 0) DegreeOneSmallSpectrum1490.graph fusedMap0901=true := by decide +kernel
theorem certified0901 : Certified (graph core0901) (root 10) 0 0 :=
  of_native_maps core0901 DegreeOneSmallSpectrum1491.graph DegreeOneSmallSpectrum1490.graph
    sourceMap0901 fusedMap0901 sourceMap0901_checked fusedMap0901_checked
    DegreeTwoThreeFiniteComparisons.comparison0901
#print axioms sourceMap0901_checked
#print axioms fusedMap0901_checked
#print axioms certified0901
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
