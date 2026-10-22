/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0541 : Family 10 := level10.get ⟨520,by decide⟩
def sourceMap0541 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0541 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0541_checked : acceptsGraphIso
    (source (graph core0541) (root 10) 0 0) DegreeTwoThreeSpectrum1382.graph sourceMap0541=true := by decide +kernel
theorem fusedMap0541_checked : acceptsGraphIso
    (fused (graph core0541) (root 10) 0 0) DegreeOneSmallSpectrum1013.graph fusedMap0541=true := by decide +kernel
theorem certified0541 : Certified (graph core0541) (root 10) 0 0 :=
  of_native_maps core0541 DegreeTwoThreeSpectrum1382.graph DegreeOneSmallSpectrum1013.graph
    sourceMap0541 fusedMap0541 sourceMap0541_checked fusedMap0541_checked
    DegreeTwoThreeFiniteComparisons.comparison0541
#print axioms sourceMap0541_checked
#print axioms fusedMap0541_checked
#print axioms certified0541
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
