/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0176 : Family 9 := level9.get ⟨83,by decide⟩
def sourceMap0176 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0176 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0176_checked : acceptsGraphIso
    (source (graph core0176) (root 9) 0 0) DegreeOneSmallSpectrum422.graph sourceMap0176=true := by decide +kernel
theorem fusedMap0176_checked : acceptsGraphIso
    (fused (graph core0176) (root 9) 0 0) DegreeOneSmallSpectrum546.graph fusedMap0176=true := by decide +kernel
theorem certified0176 : Certified (graph core0176) (root 9) 0 0 :=
  of_native_maps core0176 DegreeOneSmallSpectrum422.graph DegreeOneSmallSpectrum546.graph
    sourceMap0176 fusedMap0176 sourceMap0176_checked fusedMap0176_checked
    DegreeTwoThreeFiniteComparisons.comparison0176
#print axioms sourceMap0176_checked
#print axioms fusedMap0176_checked
#print axioms certified0176
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
