/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0350 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0350 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0350 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0350_checked : acceptsGraphIso
    (source (graph core0350) (root 6) 0 2) DegreeOneSmallSpectrum206.graph sourceMap0350=true := by decide +kernel
theorem fusedMap0350_checked : acceptsGraphIso
    (fused (graph core0350) (root 6) 0 2) DegreeOneSmallSpectrum207.graph fusedMap0350=true := by decide +kernel
theorem certified0350 : Certified (graph core0350) (root 6) 0 2 :=
  of_native_maps core0350 DegreeOneSmallSpectrum206.graph DegreeOneSmallSpectrum207.graph
    sourceMap0350 fusedMap0350 sourceMap0350_checked fusedMap0350_checked
    DegreeOneSmallComparisons.comparison0350
#print axioms sourceMap0350_checked
#print axioms fusedMap0350_checked
#print axioms certified0350
def sourceMap0350swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0350swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0350swap_checked : acceptsGraphIso
    (source (graph core0350) (root 6) 2 0) DegreeOneSmallSpectrum206.graph sourceMap0350swap=true := by decide +kernel
theorem fusedMap0350swap_checked : acceptsGraphIso
    (fused (graph core0350) (root 6) 2 0) DegreeOneSmallSpectrum207.graph fusedMap0350swap=true := by decide +kernel
theorem certified0350swap : Certified (graph core0350) (root 6) 2 0 :=
  of_native_maps core0350 DegreeOneSmallSpectrum206.graph DegreeOneSmallSpectrum207.graph
    sourceMap0350swap fusedMap0350swap sourceMap0350swap_checked fusedMap0350swap_checked
    DegreeOneSmallComparisons.comparison0350
#print axioms sourceMap0350swap_checked
#print axioms fusedMap0350swap_checked
#print axioms certified0350swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
