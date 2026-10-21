/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1718 : Family 9 := level9.get ⟨499,by decide⟩
def sourceMap1718 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1718 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1718_checked : acceptsGraphIso
    (source (graph core1718) (root 9) 0 1) DegreeOneSmallSpectrum1969.graph sourceMap1718=true := by decide +kernel
theorem fusedMap1718_checked : acceptsGraphIso
    (fused (graph core1718) (root 9) 0 1) DegreeOneSmallSpectrum1476.graph fusedMap1718=true := by decide +kernel
theorem certified1718 : Certified (graph core1718) (root 9) 0 1 :=
  of_native_maps core1718 DegreeOneSmallSpectrum1969.graph DegreeOneSmallSpectrum1476.graph
    sourceMap1718 fusedMap1718 sourceMap1718_checked fusedMap1718_checked
    DegreeOneSmallComparisons.comparison1718
#print axioms sourceMap1718_checked
#print axioms fusedMap1718_checked
#print axioms certified1718
def sourceMap1718swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1718swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1718swap_checked : acceptsGraphIso
    (source (graph core1718) (root 9) 1 0) DegreeOneSmallSpectrum1969.graph sourceMap1718swap=true := by decide +kernel
theorem fusedMap1718swap_checked : acceptsGraphIso
    (fused (graph core1718) (root 9) 1 0) DegreeOneSmallSpectrum1476.graph fusedMap1718swap=true := by decide +kernel
theorem certified1718swap : Certified (graph core1718) (root 9) 1 0 :=
  of_native_maps core1718 DegreeOneSmallSpectrum1969.graph DegreeOneSmallSpectrum1476.graph
    sourceMap1718swap fusedMap1718swap sourceMap1718swap_checked fusedMap1718swap_checked
    DegreeOneSmallComparisons.comparison1718
#print axioms sourceMap1718swap_checked
#print axioms fusedMap1718swap_checked
#print axioms certified1718swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
