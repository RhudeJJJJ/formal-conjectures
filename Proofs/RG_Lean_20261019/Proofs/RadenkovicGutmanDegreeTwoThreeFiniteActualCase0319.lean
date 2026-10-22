/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0319 : Family 9 := level9.get ⟨479,by decide⟩
def sourceMap0319 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0319 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0319_checked : acceptsGraphIso
    (source (graph core0319) (root 9) 0 0) DegreeOneSmallSpectrum542.graph sourceMap0319=true := by decide +kernel
theorem fusedMap0319_checked : acceptsGraphIso
    (fused (graph core0319) (root 9) 0 0) DegreeOneSmallSpectrum538.graph fusedMap0319=true := by decide +kernel
theorem certified0319 : Certified (graph core0319) (root 9) 0 0 :=
  of_native_maps core0319 DegreeOneSmallSpectrum542.graph DegreeOneSmallSpectrum538.graph
    sourceMap0319 fusedMap0319 sourceMap0319_checked fusedMap0319_checked
    DegreeTwoThreeFiniteComparisons.comparison0319
#print axioms sourceMap0319_checked
#print axioms fusedMap0319_checked
#print axioms certified0319
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
