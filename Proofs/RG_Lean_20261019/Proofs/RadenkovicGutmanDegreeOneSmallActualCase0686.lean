/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0686 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0686 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0686 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0686_checked : acceptsGraphIso
    (source (graph core0686) (root 7) 1 2) DegreeOneSmallSpectrum1636.graph sourceMap0686=true := by decide +kernel
theorem fusedMap0686_checked : acceptsGraphIso
    (fused (graph core0686) (root 7) 1 2) DegreeOneSmallSpectrum1015.graph fusedMap0686=true := by decide +kernel
theorem certified0686 : Certified (graph core0686) (root 7) 1 2 :=
  of_native_maps core0686 DegreeOneSmallSpectrum1636.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0686 fusedMap0686 sourceMap0686_checked fusedMap0686_checked
    DegreeOneSmallComparisons.comparison0686
#print axioms sourceMap0686_checked
#print axioms fusedMap0686_checked
#print axioms certified0686
def sourceMap0686swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0686swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0686swap_checked : acceptsGraphIso
    (source (graph core0686) (root 7) 2 1) DegreeOneSmallSpectrum1636.graph sourceMap0686swap=true := by decide +kernel
theorem fusedMap0686swap_checked : acceptsGraphIso
    (fused (graph core0686) (root 7) 2 1) DegreeOneSmallSpectrum1015.graph fusedMap0686swap=true := by decide +kernel
theorem certified0686swap : Certified (graph core0686) (root 7) 2 1 :=
  of_native_maps core0686 DegreeOneSmallSpectrum1636.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0686swap fusedMap0686swap sourceMap0686swap_checked fusedMap0686swap_checked
    DegreeOneSmallComparisons.comparison0686
#print axioms sourceMap0686swap_checked
#print axioms fusedMap0686swap_checked
#print axioms certified0686swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
