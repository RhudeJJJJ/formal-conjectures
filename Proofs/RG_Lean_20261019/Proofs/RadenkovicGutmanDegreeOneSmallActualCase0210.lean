/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0210 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0210 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap0210 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0210_checked : acceptsGraphIso
    (source (graph core0210) (root 5) 0 3) DegreeOneSmallSpectrum171.graph sourceMap0210=true := by decide +kernel
theorem fusedMap0210_checked : acceptsGraphIso
    (fused (graph core0210) (root 5) 0 3) DegreeOneSmallSpectrum175.graph fusedMap0210=true := by decide +kernel
theorem certified0210 : Certified (graph core0210) (root 5) 0 3 :=
  of_native_maps core0210 DegreeOneSmallSpectrum171.graph DegreeOneSmallSpectrum175.graph
    sourceMap0210 fusedMap0210 sourceMap0210_checked fusedMap0210_checked
    DegreeOneSmallComparisons.comparison0210
#print axioms sourceMap0210_checked
#print axioms fusedMap0210_checked
#print axioms certified0210
def sourceMap0210swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,6] (sourceLabel 5 3 0 v)
def fusedMap0210swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0210swap_checked : acceptsGraphIso
    (source (graph core0210) (root 5) 3 0) DegreeOneSmallSpectrum171.graph sourceMap0210swap=true := by decide +kernel
theorem fusedMap0210swap_checked : acceptsGraphIso
    (fused (graph core0210) (root 5) 3 0) DegreeOneSmallSpectrum175.graph fusedMap0210swap=true := by decide +kernel
theorem certified0210swap : Certified (graph core0210) (root 5) 3 0 :=
  of_native_maps core0210 DegreeOneSmallSpectrum171.graph DegreeOneSmallSpectrum175.graph
    sourceMap0210swap fusedMap0210swap sourceMap0210swap_checked fusedMap0210swap_checked
    DegreeOneSmallComparisons.comparison0210
#print axioms sourceMap0210swap_checked
#print axioms fusedMap0210swap_checked
#print axioms certified0210swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
