/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1766 : Family 9 := level9.get ⟨689,by decide⟩
def sourceMap1766 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1766 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1766_checked : acceptsGraphIso
    (source (graph core1766) (root 9) 0 1) DegreeOneSmallSpectrum1990.graph sourceMap1766=true := by decide +kernel
theorem fusedMap1766_checked : acceptsGraphIso
    (fused (graph core1766) (root 9) 0 1) DegreeOneSmallSpectrum1517.graph fusedMap1766=true := by decide +kernel
theorem certified1766 : Certified (graph core1766) (root 9) 0 1 :=
  of_native_maps core1766 DegreeOneSmallSpectrum1990.graph DegreeOneSmallSpectrum1517.graph
    sourceMap1766 fusedMap1766 sourceMap1766_checked fusedMap1766_checked
    DegreeOneSmallComparisons.comparison1766
#print axioms sourceMap1766_checked
#print axioms fusedMap1766_checked
#print axioms certified1766
def sourceMap1766swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1766swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1766swap_checked : acceptsGraphIso
    (source (graph core1766) (root 9) 1 0) DegreeOneSmallSpectrum1990.graph sourceMap1766swap=true := by decide +kernel
theorem fusedMap1766swap_checked : acceptsGraphIso
    (fused (graph core1766) (root 9) 1 0) DegreeOneSmallSpectrum1517.graph fusedMap1766swap=true := by decide +kernel
theorem certified1766swap : Certified (graph core1766) (root 9) 1 0 :=
  of_native_maps core1766 DegreeOneSmallSpectrum1990.graph DegreeOneSmallSpectrum1517.graph
    sourceMap1766swap fusedMap1766swap sourceMap1766swap_checked fusedMap1766swap_checked
    DegreeOneSmallComparisons.comparison1766
#print axioms sourceMap1766swap_checked
#print axioms fusedMap1766swap_checked
#print axioms certified1766swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
