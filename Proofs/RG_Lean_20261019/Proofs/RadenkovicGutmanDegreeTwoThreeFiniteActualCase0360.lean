/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0360 : Family 9 := level9.get ⟨578,by decide⟩
def sourceMap0360 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0360 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0360_checked : acceptsGraphIso
    (source (graph core0360) (root 9) 0 0) DegreeOneSmallSpectrum668.graph sourceMap0360=true := by decide +kernel
theorem fusedMap0360_checked : acceptsGraphIso
    (fused (graph core0360) (root 9) 0 0) DegreeOneSmallSpectrum667.graph fusedMap0360=true := by decide +kernel
theorem certified0360 : Certified (graph core0360) (root 9) 0 0 :=
  of_native_maps core0360 DegreeOneSmallSpectrum668.graph DegreeOneSmallSpectrum667.graph
    sourceMap0360 fusedMap0360 sourceMap0360_checked fusedMap0360_checked
    DegreeTwoThreeFiniteComparisons.comparison0360
#print axioms sourceMap0360_checked
#print axioms fusedMap0360_checked
#print axioms certified0360
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
