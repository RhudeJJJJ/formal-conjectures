/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1758 : Family 9 := level9.get ⟨629,by decide⟩
def sourceMap1758 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1758 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1758_checked : acceptsGraphIso
    (source (graph core1758) (root 9) 0 1) DegreeOneSmallSpectrum1886.graph sourceMap1758=true := by decide +kernel
theorem fusedMap1758_checked : acceptsGraphIso
    (fused (graph core1758) (root 9) 0 1) DegreeOneSmallSpectrum1887.graph fusedMap1758=true := by decide +kernel
theorem certified1758 : Certified (graph core1758) (root 9) 0 1 :=
  of_native_maps core1758 DegreeOneSmallSpectrum1886.graph DegreeOneSmallSpectrum1887.graph
    sourceMap1758 fusedMap1758 sourceMap1758_checked fusedMap1758_checked
    DegreeOneSmallComparisons.comparison1758
#print axioms sourceMap1758_checked
#print axioms fusedMap1758_checked
#print axioms certified1758
def sourceMap1758swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1758swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1758swap_checked : acceptsGraphIso
    (source (graph core1758) (root 9) 1 0) DegreeOneSmallSpectrum1886.graph sourceMap1758swap=true := by decide +kernel
theorem fusedMap1758swap_checked : acceptsGraphIso
    (fused (graph core1758) (root 9) 1 0) DegreeOneSmallSpectrum1887.graph fusedMap1758swap=true := by decide +kernel
theorem certified1758swap : Certified (graph core1758) (root 9) 1 0 :=
  of_native_maps core1758 DegreeOneSmallSpectrum1886.graph DegreeOneSmallSpectrum1887.graph
    sourceMap1758swap fusedMap1758swap sourceMap1758swap_checked fusedMap1758swap_checked
    DegreeOneSmallComparisons.comparison1758
#print axioms sourceMap1758swap_checked
#print axioms fusedMap1758swap_checked
#print axioms certified1758swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
