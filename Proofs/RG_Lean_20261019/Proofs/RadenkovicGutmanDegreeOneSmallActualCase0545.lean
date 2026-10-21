/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0545 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0545 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap0545 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0545_checked : acceptsGraphIso
    (source (graph core0545) (root 7) 0 2) DegreeOneSmallSpectrum582.graph sourceMap0545=true := by decide +kernel
theorem fusedMap0545_checked : acceptsGraphIso
    (fused (graph core0545) (root 7) 0 2) DegreeOneSmallSpectrum389.graph fusedMap0545=true := by decide +kernel
theorem certified0545 : Certified (graph core0545) (root 7) 0 2 :=
  of_native_maps core0545 DegreeOneSmallSpectrum582.graph DegreeOneSmallSpectrum389.graph
    sourceMap0545 fusedMap0545 sourceMap0545_checked fusedMap0545_checked
    DegreeOneSmallComparisons.comparison0545
#print axioms sourceMap0545_checked
#print axioms fusedMap0545_checked
#print axioms certified0545
def sourceMap0545swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 2 0 v)
def fusedMap0545swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0545swap_checked : acceptsGraphIso
    (source (graph core0545) (root 7) 2 0) DegreeOneSmallSpectrum582.graph sourceMap0545swap=true := by decide +kernel
theorem fusedMap0545swap_checked : acceptsGraphIso
    (fused (graph core0545) (root 7) 2 0) DegreeOneSmallSpectrum389.graph fusedMap0545swap=true := by decide +kernel
theorem certified0545swap : Certified (graph core0545) (root 7) 2 0 :=
  of_native_maps core0545 DegreeOneSmallSpectrum582.graph DegreeOneSmallSpectrum389.graph
    sourceMap0545swap fusedMap0545swap sourceMap0545swap_checked fusedMap0545swap_checked
    DegreeOneSmallComparisons.comparison0545
#print axioms sourceMap0545swap_checked
#print axioms fusedMap0545swap_checked
#print axioms certified0545swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
