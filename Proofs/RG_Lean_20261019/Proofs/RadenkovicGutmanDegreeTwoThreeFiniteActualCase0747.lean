/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0747 : Family 10 := level10.get ⟨1081,by decide⟩
def sourceMap0747 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0747 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0747_checked : acceptsGraphIso
    (source (graph core0747) (root 10) 0 0) DegreeOneSmallSpectrum1057.graph sourceMap0747=true := by decide +kernel
theorem fusedMap0747_checked : acceptsGraphIso
    (fused (graph core0747) (root 10) 0 0) DegreeOneSmallSpectrum1056.graph fusedMap0747=true := by decide +kernel
theorem certified0747 : Certified (graph core0747) (root 10) 0 0 :=
  of_native_maps core0747 DegreeOneSmallSpectrum1057.graph DegreeOneSmallSpectrum1056.graph
    sourceMap0747 fusedMap0747 sourceMap0747_checked fusedMap0747_checked
    DegreeTwoThreeFiniteComparisons.comparison0747
#print axioms sourceMap0747_checked
#print axioms fusedMap0747_checked
#print axioms certified0747
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
