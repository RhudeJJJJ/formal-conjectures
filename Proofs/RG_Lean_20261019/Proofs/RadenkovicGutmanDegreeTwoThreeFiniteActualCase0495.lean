/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0495 : Family 10 := level10.get ⟨384,by decide⟩
def sourceMap0495 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0495 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0495_checked : acceptsGraphIso
    (source (graph core0495) (root 10) 0 0) DegreeOneSmallSpectrum1056.graph sourceMap0495=true := by decide +kernel
theorem fusedMap0495_checked : acceptsGraphIso
    (fused (graph core0495) (root 10) 0 0) DegreeOneSmallSpectrum1446.graph fusedMap0495=true := by decide +kernel
theorem certified0495 : Certified (graph core0495) (root 10) 0 0 :=
  of_native_maps core0495 DegreeOneSmallSpectrum1056.graph DegreeOneSmallSpectrum1446.graph
    sourceMap0495 fusedMap0495 sourceMap0495_checked fusedMap0495_checked
    DegreeTwoThreeFiniteComparisons.comparison0495
#print axioms sourceMap0495_checked
#print axioms fusedMap0495_checked
#print axioms certified0495
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
