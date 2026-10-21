/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0897 : Family 8 := level8.get ⟨54,by decide⟩
def sourceMap0897 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0897 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0897_checked : acceptsGraphIso
    (source (graph core0897) (root 8) 0 2) DegreeOneSmallSpectrum1330.graph sourceMap0897=true := by decide +kernel
theorem fusedMap0897_checked : acceptsGraphIso
    (fused (graph core0897) (root 8) 0 2) DegreeOneSmallSpectrum910.graph fusedMap0897=true := by decide +kernel
theorem certified0897 : Certified (graph core0897) (root 8) 0 2 :=
  of_native_maps core0897 DegreeOneSmallSpectrum1330.graph DegreeOneSmallSpectrum910.graph
    sourceMap0897 fusedMap0897 sourceMap0897_checked fusedMap0897_checked
    DegreeOneSmallComparisons.comparison0897
#print axioms sourceMap0897_checked
#print axioms fusedMap0897_checked
#print axioms certified0897
def sourceMap0897swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0897swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0897swap_checked : acceptsGraphIso
    (source (graph core0897) (root 8) 2 0) DegreeOneSmallSpectrum1330.graph sourceMap0897swap=true := by decide +kernel
theorem fusedMap0897swap_checked : acceptsGraphIso
    (fused (graph core0897) (root 8) 2 0) DegreeOneSmallSpectrum910.graph fusedMap0897swap=true := by decide +kernel
theorem certified0897swap : Certified (graph core0897) (root 8) 2 0 :=
  of_native_maps core0897 DegreeOneSmallSpectrum1330.graph DegreeOneSmallSpectrum910.graph
    sourceMap0897swap fusedMap0897swap sourceMap0897swap_checked fusedMap0897swap_checked
    DegreeOneSmallComparisons.comparison0897
#print axioms sourceMap0897swap_checked
#print axioms fusedMap0897swap_checked
#print axioms certified0897swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
