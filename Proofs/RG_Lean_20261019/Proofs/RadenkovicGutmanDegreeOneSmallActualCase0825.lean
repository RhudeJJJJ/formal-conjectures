/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0825 : Family 8 := level8.get ⟨26,by decide⟩
def sourceMap0825 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0825 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0825_checked : acceptsGraphIso
    (source (graph core0825) (root 8) 0 2) DegreeOneSmallSpectrum964.graph sourceMap0825=true := by decide +kernel
theorem fusedMap0825_checked : acceptsGraphIso
    (fused (graph core0825) (root 8) 0 2) DegreeOneSmallSpectrum974.graph fusedMap0825=true := by decide +kernel
theorem certified0825 : Certified (graph core0825) (root 8) 0 2 :=
  of_native_maps core0825 DegreeOneSmallSpectrum964.graph DegreeOneSmallSpectrum974.graph
    sourceMap0825 fusedMap0825 sourceMap0825_checked fusedMap0825_checked
    DegreeOneSmallComparisons.comparison0825
#print axioms sourceMap0825_checked
#print axioms fusedMap0825_checked
#print axioms certified0825
def sourceMap0825swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0825swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0825swap_checked : acceptsGraphIso
    (source (graph core0825) (root 8) 2 0) DegreeOneSmallSpectrum964.graph sourceMap0825swap=true := by decide +kernel
theorem fusedMap0825swap_checked : acceptsGraphIso
    (fused (graph core0825) (root 8) 2 0) DegreeOneSmallSpectrum974.graph fusedMap0825swap=true := by decide +kernel
theorem certified0825swap : Certified (graph core0825) (root 8) 2 0 :=
  of_native_maps core0825 DegreeOneSmallSpectrum964.graph DegreeOneSmallSpectrum974.graph
    sourceMap0825swap fusedMap0825swap sourceMap0825swap_checked fusedMap0825swap_checked
    DegreeOneSmallComparisons.comparison0825
#print axioms sourceMap0825swap_checked
#print axioms fusedMap0825swap_checked
#print axioms certified0825swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
