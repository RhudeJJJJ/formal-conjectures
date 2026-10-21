/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0182 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0182 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (sourceLabel 5 2 3 v)
def fusedMap0182 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0182_checked : acceptsGraphIso
    (source (graph core0182) (root 5) 2 3) DegreeOneSmallSpectrum1288.graph sourceMap0182=true := by decide +kernel
theorem fusedMap0182_checked : acceptsGraphIso
    (fused (graph core0182) (root 5) 2 3) DegreeOneSmallSpectrum856.graph fusedMap0182=true := by decide +kernel
theorem certified0182 : Certified (graph core0182) (root 5) 2 3 :=
  of_native_maps core0182 DegreeOneSmallSpectrum1288.graph DegreeOneSmallSpectrum856.graph
    sourceMap0182 fusedMap0182 sourceMap0182_checked fusedMap0182_checked
    DegreeOneSmallComparisons.comparison0182
#print axioms sourceMap0182_checked
#print axioms fusedMap0182_checked
#print axioms certified0182
def sourceMap0182swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 3 2 v)
def fusedMap0182swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0182swap_checked : acceptsGraphIso
    (source (graph core0182) (root 5) 3 2) DegreeOneSmallSpectrum1288.graph sourceMap0182swap=true := by decide +kernel
theorem fusedMap0182swap_checked : acceptsGraphIso
    (fused (graph core0182) (root 5) 3 2) DegreeOneSmallSpectrum856.graph fusedMap0182swap=true := by decide +kernel
theorem certified0182swap : Certified (graph core0182) (root 5) 3 2 :=
  of_native_maps core0182 DegreeOneSmallSpectrum1288.graph DegreeOneSmallSpectrum856.graph
    sourceMap0182swap fusedMap0182swap sourceMap0182swap_checked fusedMap0182swap_checked
    DegreeOneSmallComparisons.comparison0182
#print axioms sourceMap0182swap_checked
#print axioms fusedMap0182swap_checked
#print axioms certified0182swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
