/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0330 : Family 9 := level9.get ⟨506,by decide⟩
def sourceMap0330 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0330 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0330_checked : acceptsGraphIso
    (source (graph core0330) (root 9) 0 0) DegreeOneSmallSpectrum727.graph sourceMap0330=true := by decide +kernel
theorem fusedMap0330_checked : acceptsGraphIso
    (fused (graph core0330) (root 9) 0 0) DegreeOneSmallSpectrum707.graph fusedMap0330=true := by decide +kernel
theorem certified0330 : Certified (graph core0330) (root 9) 0 0 :=
  of_native_maps core0330 DegreeOneSmallSpectrum727.graph DegreeOneSmallSpectrum707.graph
    sourceMap0330 fusedMap0330 sourceMap0330_checked fusedMap0330_checked
    DegreeTwoThreeFiniteComparisons.comparison0330
#print axioms sourceMap0330_checked
#print axioms fusedMap0330_checked
#print axioms certified0330
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
