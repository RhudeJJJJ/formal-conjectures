/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1762 : Family 9 := level9.get ⟨634,by decide⟩
def sourceMap1762 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1762 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1762_checked : acceptsGraphIso
    (source (graph core1762) (root 9) 0 1) DegreeOneSmallSpectrum1899.graph sourceMap1762=true := by decide +kernel
theorem fusedMap1762_checked : acceptsGraphIso
    (fused (graph core1762) (root 9) 0 1) DegreeOneSmallSpectrum1900.graph fusedMap1762=true := by decide +kernel
theorem certified1762 : Certified (graph core1762) (root 9) 0 1 :=
  of_native_maps core1762 DegreeOneSmallSpectrum1899.graph DegreeOneSmallSpectrum1900.graph
    sourceMap1762 fusedMap1762 sourceMap1762_checked fusedMap1762_checked
    DegreeOneSmallComparisons.comparison1762
#print axioms sourceMap1762_checked
#print axioms fusedMap1762_checked
#print axioms certified1762
def sourceMap1762swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1762swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1762swap_checked : acceptsGraphIso
    (source (graph core1762) (root 9) 1 0) DegreeOneSmallSpectrum1899.graph sourceMap1762swap=true := by decide +kernel
theorem fusedMap1762swap_checked : acceptsGraphIso
    (fused (graph core1762) (root 9) 1 0) DegreeOneSmallSpectrum1900.graph fusedMap1762swap=true := by decide +kernel
theorem certified1762swap : Certified (graph core1762) (root 9) 1 0 :=
  of_native_maps core1762 DegreeOneSmallSpectrum1899.graph DegreeOneSmallSpectrum1900.graph
    sourceMap1762swap fusedMap1762swap sourceMap1762swap_checked fusedMap1762swap_checked
    DegreeOneSmallComparisons.comparison1762
#print axioms sourceMap1762swap_checked
#print axioms fusedMap1762swap_checked
#print axioms certified1762swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
