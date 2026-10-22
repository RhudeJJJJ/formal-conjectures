/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0326 : Family 9 := level9.get ⟨500,by decide⟩
def sourceMap0326 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,5,6,7,8,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0326 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0326_checked : acceptsGraphIso
    (source (graph core0326) (root 9) 0 0) DegreeOneSmallSpectrum631.graph sourceMap0326=true := by decide +kernel
theorem fusedMap0326_checked : acceptsGraphIso
    (fused (graph core0326) (root 9) 0 0) DegreeOneSmallSpectrum819.graph fusedMap0326=true := by decide +kernel
theorem certified0326 : Certified (graph core0326) (root 9) 0 0 :=
  of_native_maps core0326 DegreeOneSmallSpectrum631.graph DegreeOneSmallSpectrum819.graph
    sourceMap0326 fusedMap0326 sourceMap0326_checked fusedMap0326_checked
    DegreeTwoThreeFiniteComparisons.comparison0326
#print axioms sourceMap0326_checked
#print axioms fusedMap0326_checked
#print axioms certified0326
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
