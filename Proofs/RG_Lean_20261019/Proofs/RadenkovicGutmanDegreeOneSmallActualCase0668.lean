/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0668 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0668 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,4,5,1,2,3] (sourceLabel 7 1 2 v)
def fusedMap0668 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0668_checked : acceptsGraphIso
    (source (graph core0668) (root 7) 1 2) DegreeOneSmallSpectrum1487.graph sourceMap0668=true := by decide +kernel
theorem fusedMap0668_checked : acceptsGraphIso
    (fused (graph core0668) (root 7) 1 2) DegreeOneSmallSpectrum952.graph fusedMap0668=true := by decide +kernel
theorem certified0668 : Certified (graph core0668) (root 7) 1 2 :=
  of_native_maps core0668 DegreeOneSmallSpectrum1487.graph DegreeOneSmallSpectrum952.graph
    sourceMap0668 fusedMap0668 sourceMap0668_checked fusedMap0668_checked
    DegreeOneSmallComparisons.comparison0668
#print axioms sourceMap0668_checked
#print axioms fusedMap0668_checked
#print axioms certified0668
def sourceMap0668swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (sourceLabel 7 2 1 v)
def fusedMap0668swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0668swap_checked : acceptsGraphIso
    (source (graph core0668) (root 7) 2 1) DegreeOneSmallSpectrum1487.graph sourceMap0668swap=true := by decide +kernel
theorem fusedMap0668swap_checked : acceptsGraphIso
    (fused (graph core0668) (root 7) 2 1) DegreeOneSmallSpectrum952.graph fusedMap0668swap=true := by decide +kernel
theorem certified0668swap : Certified (graph core0668) (root 7) 2 1 :=
  of_native_maps core0668 DegreeOneSmallSpectrum1487.graph DegreeOneSmallSpectrum952.graph
    sourceMap0668swap fusedMap0668swap sourceMap0668swap_checked fusedMap0668swap_checked
    DegreeOneSmallComparisons.comparison0668
#print axioms sourceMap0668swap_checked
#print axioms fusedMap0668swap_checked
#print axioms certified0668swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
