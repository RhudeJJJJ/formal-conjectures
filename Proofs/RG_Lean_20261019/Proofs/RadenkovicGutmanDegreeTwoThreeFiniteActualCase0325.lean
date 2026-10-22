/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0325 : Family 9 := level9.get ⟨497,by decide⟩
def sourceMap0325 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0325 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0325_checked : acceptsGraphIso
    (source (graph core0325) (root 9) 0 0) DegreeOneSmallSpectrum809.graph sourceMap0325=true := by decide +kernel
theorem fusedMap0325_checked : acceptsGraphIso
    (fused (graph core0325) (root 9) 0 0) DegreeOneSmallSpectrum795.graph fusedMap0325=true := by decide +kernel
theorem certified0325 : Certified (graph core0325) (root 9) 0 0 :=
  of_native_maps core0325 DegreeOneSmallSpectrum809.graph DegreeOneSmallSpectrum795.graph
    sourceMap0325 fusedMap0325 sourceMap0325_checked fusedMap0325_checked
    DegreeTwoThreeFiniteComparisons.comparison0325
#print axioms sourceMap0325_checked
#print axioms fusedMap0325_checked
#print axioms certified0325
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
