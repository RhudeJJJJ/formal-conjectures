/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1742 : Family 9 := level9.get ⟨564,by decide⟩
def sourceMap1742 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1742 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1742_checked : acceptsGraphIso
    (source (graph core1742) (root 9) 0 1) DegreeOneSmallSpectrum1619.graph sourceMap1742=true := by decide +kernel
theorem fusedMap1742_checked : acceptsGraphIso
    (fused (graph core1742) (root 9) 0 1) DegreeOneSmallSpectrum1620.graph fusedMap1742=true := by decide +kernel
theorem certified1742 : Certified (graph core1742) (root 9) 0 1 :=
  of_native_maps core1742 DegreeOneSmallSpectrum1619.graph DegreeOneSmallSpectrum1620.graph
    sourceMap1742 fusedMap1742 sourceMap1742_checked fusedMap1742_checked
    DegreeOneSmallComparisons.comparison1742
#print axioms sourceMap1742_checked
#print axioms fusedMap1742_checked
#print axioms certified1742
def sourceMap1742swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1742swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1742swap_checked : acceptsGraphIso
    (source (graph core1742) (root 9) 1 0) DegreeOneSmallSpectrum1619.graph sourceMap1742swap=true := by decide +kernel
theorem fusedMap1742swap_checked : acceptsGraphIso
    (fused (graph core1742) (root 9) 1 0) DegreeOneSmallSpectrum1620.graph fusedMap1742swap=true := by decide +kernel
theorem certified1742swap : Certified (graph core1742) (root 9) 1 0 :=
  of_native_maps core1742 DegreeOneSmallSpectrum1619.graph DegreeOneSmallSpectrum1620.graph
    sourceMap1742swap fusedMap1742swap sourceMap1742swap_checked fusedMap1742swap_checked
    DegreeOneSmallComparisons.comparison1742
#print axioms sourceMap1742swap_checked
#print axioms fusedMap1742swap_checked
#print axioms certified1742swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
