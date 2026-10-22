/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0352 : Family 9 := level9.get ⟨563,by decide⟩
def sourceMap0352 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0352 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0352_checked : acceptsGraphIso
    (source (graph core0352) (root 9) 0 0) DegreeOneSmallSpectrum842.graph sourceMap0352=true := by decide +kernel
theorem fusedMap0352_checked : acceptsGraphIso
    (fused (graph core0352) (root 9) 0 0) DegreeOneSmallSpectrum629.graph fusedMap0352=true := by decide +kernel
theorem certified0352 : Certified (graph core0352) (root 9) 0 0 :=
  of_native_maps core0352 DegreeOneSmallSpectrum842.graph DegreeOneSmallSpectrum629.graph
    sourceMap0352 fusedMap0352 sourceMap0352_checked fusedMap0352_checked
    DegreeTwoThreeFiniteComparisons.comparison0352
#print axioms sourceMap0352_checked
#print axioms fusedMap0352_checked
#print axioms certified0352
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
