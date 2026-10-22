/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0570 : Family 10 := level10.get ⟨609,by decide⟩
def sourceMap0570 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0570 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0570_checked : acceptsGraphIso
    (source (graph core0570) (root 10) 0 0) DegreeOneSmallSpectrum1168.graph sourceMap0570=true := by decide +kernel
theorem fusedMap0570_checked : acceptsGraphIso
    (fused (graph core0570) (root 10) 0 0) DegreeOneSmallSpectrum1165.graph fusedMap0570=true := by decide +kernel
theorem certified0570 : Certified (graph core0570) (root 10) 0 0 :=
  of_native_maps core0570 DegreeOneSmallSpectrum1168.graph DegreeOneSmallSpectrum1165.graph
    sourceMap0570 fusedMap0570 sourceMap0570_checked fusedMap0570_checked
    DegreeTwoThreeFiniteComparisons.comparison0570
#print axioms sourceMap0570_checked
#print axioms fusedMap0570_checked
#print axioms certified0570
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
