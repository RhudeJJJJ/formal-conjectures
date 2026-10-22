/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0216 : Family 9 := level9.get ⟨211,by decide⟩
def sourceMap0216 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0216 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0216_checked : acceptsGraphIso
    (source (graph core0216) (root 9) 0 0) DegreeOneSmallSpectrum512.graph sourceMap0216=true := by decide +kernel
theorem fusedMap0216_checked : acceptsGraphIso
    (fused (graph core0216) (root 9) 0 0) DegreeOneSmallSpectrum511.graph fusedMap0216=true := by decide +kernel
theorem certified0216 : Certified (graph core0216) (root 9) 0 0 :=
  of_native_maps core0216 DegreeOneSmallSpectrum512.graph DegreeOneSmallSpectrum511.graph
    sourceMap0216 fusedMap0216 sourceMap0216_checked fusedMap0216_checked
    DegreeTwoThreeFiniteComparisons.comparison0216
#print axioms sourceMap0216_checked
#print axioms fusedMap0216_checked
#print axioms certified0216
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
