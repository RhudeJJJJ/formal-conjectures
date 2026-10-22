/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0320 : Family 9 := level9.get ⟨481,by decide⟩
def sourceMap0320 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0320 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0320_checked : acceptsGraphIso
    (source (graph core0320) (root 9) 0 0) DegreeOneSmallSpectrum648.graph sourceMap0320=true := by decide +kernel
theorem fusedMap0320_checked : acceptsGraphIso
    (fused (graph core0320) (root 9) 0 0) DegreeOneSmallSpectrum639.graph fusedMap0320=true := by decide +kernel
theorem certified0320 : Certified (graph core0320) (root 9) 0 0 :=
  of_native_maps core0320 DegreeOneSmallSpectrum648.graph DegreeOneSmallSpectrum639.graph
    sourceMap0320 fusedMap0320 sourceMap0320_checked fusedMap0320_checked
    DegreeTwoThreeFiniteComparisons.comparison0320
#print axioms sourceMap0320_checked
#print axioms fusedMap0320_checked
#print axioms certified0320
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
