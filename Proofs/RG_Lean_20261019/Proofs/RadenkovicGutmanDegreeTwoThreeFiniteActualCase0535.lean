/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0535 : Family 10 := level10.get ⟨492,by decide⟩
def sourceMap0535 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0535 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0535_checked : acceptsGraphIso
    (source (graph core0535) (root 10) 0 0) DegreeOneSmallSpectrum1021.graph sourceMap0535=true := by decide +kernel
theorem fusedMap0535_checked : acceptsGraphIso
    (fused (graph core0535) (root 10) 0 0) DegreeOneSmallSpectrum1015.graph fusedMap0535=true := by decide +kernel
theorem certified0535 : Certified (graph core0535) (root 10) 0 0 :=
  of_native_maps core0535 DegreeOneSmallSpectrum1021.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0535 fusedMap0535 sourceMap0535_checked fusedMap0535_checked
    DegreeTwoThreeFiniteComparisons.comparison0535
#print axioms sourceMap0535_checked
#print axioms fusedMap0535_checked
#print axioms certified0535
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
