/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0492 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0492 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0492 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0492_checked : acceptsGraphIso
    (source (graph core0492) (root 7) 0 3) DegreeOneSmallSpectrum878.graph sourceMap0492=true := by decide +kernel
theorem fusedMap0492_checked : acceptsGraphIso
    (fused (graph core0492) (root 7) 0 3) DegreeOneSmallSpectrum879.graph fusedMap0492=true := by decide +kernel
theorem certified0492 : Certified (graph core0492) (root 7) 0 3 :=
  of_native_maps core0492 DegreeOneSmallSpectrum878.graph DegreeOneSmallSpectrum879.graph
    sourceMap0492 fusedMap0492 sourceMap0492_checked fusedMap0492_checked
    DegreeOneSmallComparisons.comparison0492
#print axioms sourceMap0492_checked
#print axioms fusedMap0492_checked
#print axioms certified0492
def sourceMap0492swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0492swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0492swap_checked : acceptsGraphIso
    (source (graph core0492) (root 7) 3 0) DegreeOneSmallSpectrum878.graph sourceMap0492swap=true := by decide +kernel
theorem fusedMap0492swap_checked : acceptsGraphIso
    (fused (graph core0492) (root 7) 3 0) DegreeOneSmallSpectrum879.graph fusedMap0492swap=true := by decide +kernel
theorem certified0492swap : Certified (graph core0492) (root 7) 3 0 :=
  of_native_maps core0492 DegreeOneSmallSpectrum878.graph DegreeOneSmallSpectrum879.graph
    sourceMap0492swap fusedMap0492swap sourceMap0492swap_checked fusedMap0492swap_checked
    DegreeOneSmallComparisons.comparison0492
#print axioms sourceMap0492swap_checked
#print axioms fusedMap0492swap_checked
#print axioms certified0492swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
