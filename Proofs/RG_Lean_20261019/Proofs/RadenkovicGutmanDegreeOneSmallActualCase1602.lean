/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1602 : Family 9 := level9.get ⟨342,by decide⟩
def sourceMap1602 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1602 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1602_checked : acceptsGraphIso
    (source (graph core1602) (root 9) 0 1) DegreeOneSmallSpectrum1687.graph sourceMap1602=true := by decide +kernel
theorem fusedMap1602_checked : acceptsGraphIso
    (fused (graph core1602) (root 9) 0 1) DegreeOneSmallSpectrum1038.graph fusedMap1602=true := by decide +kernel
theorem certified1602 : Certified (graph core1602) (root 9) 0 1 :=
  of_native_maps core1602 DegreeOneSmallSpectrum1687.graph DegreeOneSmallSpectrum1038.graph
    sourceMap1602 fusedMap1602 sourceMap1602_checked fusedMap1602_checked
    DegreeOneSmallComparisons.comparison1602
#print axioms sourceMap1602_checked
#print axioms fusedMap1602_checked
#print axioms certified1602
def sourceMap1602swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1602swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1602swap_checked : acceptsGraphIso
    (source (graph core1602) (root 9) 1 0) DegreeOneSmallSpectrum1687.graph sourceMap1602swap=true := by decide +kernel
theorem fusedMap1602swap_checked : acceptsGraphIso
    (fused (graph core1602) (root 9) 1 0) DegreeOneSmallSpectrum1038.graph fusedMap1602swap=true := by decide +kernel
theorem certified1602swap : Certified (graph core1602) (root 9) 1 0 :=
  of_native_maps core1602 DegreeOneSmallSpectrum1687.graph DegreeOneSmallSpectrum1038.graph
    sourceMap1602swap fusedMap1602swap sourceMap1602swap_checked fusedMap1602swap_checked
    DegreeOneSmallComparisons.comparison1602
#print axioms sourceMap1602swap_checked
#print axioms fusedMap1602swap_checked
#print axioms certified1602swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
