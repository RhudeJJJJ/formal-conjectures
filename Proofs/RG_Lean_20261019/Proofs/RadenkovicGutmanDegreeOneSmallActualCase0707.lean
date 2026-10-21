/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0707 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0707 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0707 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0707_checked : acceptsGraphIso
    (source (graph core0707) (root 7) 0 2) DegreeOneSmallSpectrum718.graph sourceMap0707=true := by decide +kernel
theorem fusedMap0707_checked : acceptsGraphIso
    (fused (graph core0707) (root 7) 0 2) SmallGeFourSpectrum095.graph fusedMap0707=true := by decide +kernel
theorem certified0707 : Certified (graph core0707) (root 7) 0 2 :=
  of_native_maps core0707 DegreeOneSmallSpectrum718.graph SmallGeFourSpectrum095.graph
    sourceMap0707 fusedMap0707 sourceMap0707_checked fusedMap0707_checked
    DegreeOneSmallComparisons.comparison0707
#print axioms sourceMap0707_checked
#print axioms fusedMap0707_checked
#print axioms certified0707
def sourceMap0707swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0707swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0707swap_checked : acceptsGraphIso
    (source (graph core0707) (root 7) 2 0) DegreeOneSmallSpectrum718.graph sourceMap0707swap=true := by decide +kernel
theorem fusedMap0707swap_checked : acceptsGraphIso
    (fused (graph core0707) (root 7) 2 0) SmallGeFourSpectrum095.graph fusedMap0707swap=true := by decide +kernel
theorem certified0707swap : Certified (graph core0707) (root 7) 2 0 :=
  of_native_maps core0707 DegreeOneSmallSpectrum718.graph SmallGeFourSpectrum095.graph
    sourceMap0707swap fusedMap0707swap sourceMap0707swap_checked fusedMap0707swap_checked
    DegreeOneSmallComparisons.comparison0707
#print axioms sourceMap0707swap_checked
#print axioms fusedMap0707swap_checked
#print axioms certified0707swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
