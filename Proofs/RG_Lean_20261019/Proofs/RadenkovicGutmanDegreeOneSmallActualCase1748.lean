/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1748 : Family 9 := level9.get ⟨585,by decide⟩
def sourceMap1748 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1748 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1748_checked : acceptsGraphIso
    (source (graph core1748) (root 9) 0 1) DegreeOneSmallSpectrum1700.graph sourceMap1748=true := by decide +kernel
theorem fusedMap1748_checked : acceptsGraphIso
    (fused (graph core1748) (root 9) 0 1) DegreeOneSmallSpectrum1701.graph fusedMap1748=true := by decide +kernel
theorem certified1748 : Certified (graph core1748) (root 9) 0 1 :=
  of_native_maps core1748 DegreeOneSmallSpectrum1700.graph DegreeOneSmallSpectrum1701.graph
    sourceMap1748 fusedMap1748 sourceMap1748_checked fusedMap1748_checked
    DegreeOneSmallComparisons.comparison1748
#print axioms sourceMap1748_checked
#print axioms fusedMap1748_checked
#print axioms certified1748
def sourceMap1748swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1748swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1748swap_checked : acceptsGraphIso
    (source (graph core1748) (root 9) 1 0) DegreeOneSmallSpectrum1700.graph sourceMap1748swap=true := by decide +kernel
theorem fusedMap1748swap_checked : acceptsGraphIso
    (fused (graph core1748) (root 9) 1 0) DegreeOneSmallSpectrum1701.graph fusedMap1748swap=true := by decide +kernel
theorem certified1748swap : Certified (graph core1748) (root 9) 1 0 :=
  of_native_maps core1748 DegreeOneSmallSpectrum1700.graph DegreeOneSmallSpectrum1701.graph
    sourceMap1748swap fusedMap1748swap sourceMap1748swap_checked fusedMap1748swap_checked
    DegreeOneSmallComparisons.comparison1748
#print axioms sourceMap1748swap_checked
#print axioms fusedMap1748swap_checked
#print axioms certified1748swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
