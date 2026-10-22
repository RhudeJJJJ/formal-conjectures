/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0564 : Family 10 := level10.get ⟨594,by decide⟩
def sourceMap0564 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0564 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0564_checked : acceptsGraphIso
    (source (graph core0564) (root 10) 0 0) DegreeOneSmallSpectrum1679.graph sourceMap0564=true := by decide +kernel
theorem fusedMap0564_checked : acceptsGraphIso
    (fused (graph core0564) (root 10) 0 0) DegreeOneSmallSpectrum1140.graph fusedMap0564=true := by decide +kernel
theorem certified0564 : Certified (graph core0564) (root 10) 0 0 :=
  of_native_maps core0564 DegreeOneSmallSpectrum1679.graph DegreeOneSmallSpectrum1140.graph
    sourceMap0564 fusedMap0564 sourceMap0564_checked fusedMap0564_checked
    DegreeTwoThreeFiniteComparisons.comparison0564
#print axioms sourceMap0564_checked
#print axioms fusedMap0564_checked
#print axioms certified0564
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
