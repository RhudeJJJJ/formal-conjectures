/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0261 : Family 9 := level9.get ⟨339,by decide⟩
def sourceMap0261 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0261 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0261_checked : acceptsGraphIso
    (source (graph core0261) (root 9) 0 0) DegreeTwoThreeSpectrum562.graph sourceMap0261=true := by decide +kernel
theorem fusedMap0261_checked : acceptsGraphIso
    (fused (graph core0261) (root 9) 0 0) DegreeOneSmallSpectrum655.graph fusedMap0261=true := by decide +kernel
theorem certified0261 : Certified (graph core0261) (root 9) 0 0 :=
  of_native_maps core0261 DegreeTwoThreeSpectrum562.graph DegreeOneSmallSpectrum655.graph
    sourceMap0261 fusedMap0261 sourceMap0261_checked fusedMap0261_checked
    DegreeTwoThreeFiniteComparisons.comparison0261
#print axioms sourceMap0261_checked
#print axioms fusedMap0261_checked
#print axioms certified0261
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
