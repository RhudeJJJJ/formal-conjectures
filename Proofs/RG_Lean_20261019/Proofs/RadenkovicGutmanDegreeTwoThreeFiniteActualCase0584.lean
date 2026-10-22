/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0584 : Family 10 := level10.get ⟨649,by decide⟩
def sourceMap0584 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0584 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0584_checked : acceptsGraphIso
    (source (graph core0584) (root 10) 0 0) DegreeOneSmallSpectrum1244.graph sourceMap0584=true := by decide +kernel
theorem fusedMap0584_checked : acceptsGraphIso
    (fused (graph core0584) (root 10) 0 0) DegreeOneSmallSpectrum1242.graph fusedMap0584=true := by decide +kernel
theorem certified0584 : Certified (graph core0584) (root 10) 0 0 :=
  of_native_maps core0584 DegreeOneSmallSpectrum1244.graph DegreeOneSmallSpectrum1242.graph
    sourceMap0584 fusedMap0584 sourceMap0584_checked fusedMap0584_checked
    DegreeTwoThreeFiniteComparisons.comparison0584
#print axioms sourceMap0584_checked
#print axioms fusedMap0584_checked
#print axioms certified0584
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
