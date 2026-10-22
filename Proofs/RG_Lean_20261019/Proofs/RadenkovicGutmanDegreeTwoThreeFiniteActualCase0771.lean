/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0771 : Family 10 := level10.get ⟨1142,by decide⟩
def sourceMap0771 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0771 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0771_checked : acceptsGraphIso
    (source (graph core0771) (root 10) 0 0) DegreeOneSmallSpectrum1133.graph sourceMap0771=true := by decide +kernel
theorem fusedMap0771_checked : acceptsGraphIso
    (fused (graph core0771) (root 10) 0 0) DegreeOneSmallSpectrum1132.graph fusedMap0771=true := by decide +kernel
theorem certified0771 : Certified (graph core0771) (root 10) 0 0 :=
  of_native_maps core0771 DegreeOneSmallSpectrum1133.graph DegreeOneSmallSpectrum1132.graph
    sourceMap0771 fusedMap0771 sourceMap0771_checked fusedMap0771_checked
    DegreeTwoThreeFiniteComparisons.comparison0771
#print axioms sourceMap0771_checked
#print axioms fusedMap0771_checked
#print axioms certified0771
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
