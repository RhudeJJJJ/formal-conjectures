/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1752 : Family 9 := level9.get ⟨590,by decide⟩
def sourceMap1752 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1752 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1752_checked : acceptsGraphIso
    (source (graph core1752) (root 9) 0 1) DegreeOneSmallSpectrum1726.graph sourceMap1752=true := by decide +kernel
theorem fusedMap1752_checked : acceptsGraphIso
    (fused (graph core1752) (root 9) 0 1) DegreeOneSmallSpectrum1727.graph fusedMap1752=true := by decide +kernel
theorem certified1752 : Certified (graph core1752) (root 9) 0 1 :=
  of_native_maps core1752 DegreeOneSmallSpectrum1726.graph DegreeOneSmallSpectrum1727.graph
    sourceMap1752 fusedMap1752 sourceMap1752_checked fusedMap1752_checked
    DegreeOneSmallComparisons.comparison1752
#print axioms sourceMap1752_checked
#print axioms fusedMap1752_checked
#print axioms certified1752
def sourceMap1752swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1752swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1752swap_checked : acceptsGraphIso
    (source (graph core1752) (root 9) 1 0) DegreeOneSmallSpectrum1726.graph sourceMap1752swap=true := by decide +kernel
theorem fusedMap1752swap_checked : acceptsGraphIso
    (fused (graph core1752) (root 9) 1 0) DegreeOneSmallSpectrum1727.graph fusedMap1752swap=true := by decide +kernel
theorem certified1752swap : Certified (graph core1752) (root 9) 1 0 :=
  of_native_maps core1752 DegreeOneSmallSpectrum1726.graph DegreeOneSmallSpectrum1727.graph
    sourceMap1752swap fusedMap1752swap sourceMap1752swap_checked fusedMap1752swap_checked
    DegreeOneSmallComparisons.comparison1752
#print axioms sourceMap1752swap_checked
#print axioms fusedMap1752swap_checked
#print axioms certified1752swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
