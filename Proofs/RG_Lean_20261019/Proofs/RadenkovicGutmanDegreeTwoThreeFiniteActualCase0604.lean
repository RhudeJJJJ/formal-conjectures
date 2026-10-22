/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0604 : Family 10 := level10.get ⟨707,by decide⟩
def sourceMap0604 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0604 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0604_checked : acceptsGraphIso
    (source (graph core0604) (root 10) 0 0) DegreeOneSmallSpectrum1686.graph sourceMap0604=true := by decide +kernel
theorem fusedMap0604_checked : acceptsGraphIso
    (fused (graph core0604) (root 10) 0 0) DegreeOneSmallSpectrum1321.graph fusedMap0604=true := by decide +kernel
theorem certified0604 : Certified (graph core0604) (root 10) 0 0 :=
  of_native_maps core0604 DegreeOneSmallSpectrum1686.graph DegreeOneSmallSpectrum1321.graph
    sourceMap0604 fusedMap0604 sourceMap0604_checked fusedMap0604_checked
    DegreeTwoThreeFiniteComparisons.comparison0604
#print axioms sourceMap0604_checked
#print axioms fusedMap0604_checked
#print axioms certified0604
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
