/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0510 : Family 10 := level10.get ⟨425,by decide⟩
def sourceMap0510 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0510 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0510_checked : acceptsGraphIso
    (source (graph core0510) (root 10) 0 0) DegreeOneSmallSpectrum1134.graph sourceMap0510=true := by decide +kernel
theorem fusedMap0510_checked : acceptsGraphIso
    (fused (graph core0510) (root 10) 0 0) DegreeOneSmallSpectrum1111.graph fusedMap0510=true := by decide +kernel
theorem certified0510 : Certified (graph core0510) (root 10) 0 0 :=
  of_native_maps core0510 DegreeOneSmallSpectrum1134.graph DegreeOneSmallSpectrum1111.graph
    sourceMap0510 fusedMap0510 sourceMap0510_checked fusedMap0510_checked
    DegreeTwoThreeFiniteComparisons.comparison0510
#print axioms sourceMap0510_checked
#print axioms fusedMap0510_checked
#print axioms certified0510
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
