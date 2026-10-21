/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0917 : Family 8 := level8.get ⟨61,by decide⟩
def sourceMap0917 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0917 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0917_checked : acceptsGraphIso
    (source (graph core0917) (root 8) 0 2) DegreeOneSmallSpectrum1413.graph sourceMap0917=true := by decide +kernel
theorem fusedMap0917_checked : acceptsGraphIso
    (fused (graph core0917) (root 8) 0 2) DegreeOneSmallSpectrum923.graph fusedMap0917=true := by decide +kernel
theorem certified0917 : Certified (graph core0917) (root 8) 0 2 :=
  of_native_maps core0917 DegreeOneSmallSpectrum1413.graph DegreeOneSmallSpectrum923.graph
    sourceMap0917 fusedMap0917 sourceMap0917_checked fusedMap0917_checked
    DegreeOneSmallComparisons.comparison0917
#print axioms sourceMap0917_checked
#print axioms fusedMap0917_checked
#print axioms certified0917
def sourceMap0917swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0917swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0917swap_checked : acceptsGraphIso
    (source (graph core0917) (root 8) 2 0) DegreeOneSmallSpectrum1413.graph sourceMap0917swap=true := by decide +kernel
theorem fusedMap0917swap_checked : acceptsGraphIso
    (fused (graph core0917) (root 8) 2 0) DegreeOneSmallSpectrum923.graph fusedMap0917swap=true := by decide +kernel
theorem certified0917swap : Certified (graph core0917) (root 8) 2 0 :=
  of_native_maps core0917 DegreeOneSmallSpectrum1413.graph DegreeOneSmallSpectrum923.graph
    sourceMap0917swap fusedMap0917swap sourceMap0917swap_checked fusedMap0917swap_checked
    DegreeOneSmallComparisons.comparison0917
#print axioms sourceMap0917swap_checked
#print axioms fusedMap0917swap_checked
#print axioms certified0917swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
