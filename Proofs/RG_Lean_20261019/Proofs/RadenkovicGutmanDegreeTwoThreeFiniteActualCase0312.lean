/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0312 : Family 9 := level9.get ⟨467,by decide⟩
def sourceMap0312 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0312 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0312_checked : acceptsGraphIso
    (source (graph core0312) (root 9) 0 0) DegreeOneSmallSpectrum806.graph sourceMap0312=true := by decide +kernel
theorem fusedMap0312_checked : acceptsGraphIso
    (fused (graph core0312) (root 9) 0 0) DegreeOneSmallSpectrum792.graph fusedMap0312=true := by decide +kernel
theorem certified0312 : Certified (graph core0312) (root 9) 0 0 :=
  of_native_maps core0312 DegreeOneSmallSpectrum806.graph DegreeOneSmallSpectrum792.graph
    sourceMap0312 fusedMap0312 sourceMap0312_checked fusedMap0312_checked
    DegreeTwoThreeFiniteComparisons.comparison0312
#print axioms sourceMap0312_checked
#print axioms fusedMap0312_checked
#print axioms certified0312
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
