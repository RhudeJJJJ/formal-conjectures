/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1712 : Family 9 := level9.get ⟨492,by decide⟩
def sourceMap1712 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1712 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1712_checked : acceptsGraphIso
    (source (graph core1712) (root 9) 0 1) DegreeOneSmallSpectrum1966.graph sourceMap1712=true := by decide +kernel
theorem fusedMap1712_checked : acceptsGraphIso
    (fused (graph core1712) (root 9) 0 1) DegreeOneSmallSpectrum1465.graph fusedMap1712=true := by decide +kernel
theorem certified1712 : Certified (graph core1712) (root 9) 0 1 :=
  of_native_maps core1712 DegreeOneSmallSpectrum1966.graph DegreeOneSmallSpectrum1465.graph
    sourceMap1712 fusedMap1712 sourceMap1712_checked fusedMap1712_checked
    DegreeOneSmallComparisons.comparison1712
#print axioms sourceMap1712_checked
#print axioms fusedMap1712_checked
#print axioms certified1712
def sourceMap1712swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1712swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1712swap_checked : acceptsGraphIso
    (source (graph core1712) (root 9) 1 0) DegreeOneSmallSpectrum1966.graph sourceMap1712swap=true := by decide +kernel
theorem fusedMap1712swap_checked : acceptsGraphIso
    (fused (graph core1712) (root 9) 1 0) DegreeOneSmallSpectrum1465.graph fusedMap1712swap=true := by decide +kernel
theorem certified1712swap : Certified (graph core1712) (root 9) 1 0 :=
  of_native_maps core1712 DegreeOneSmallSpectrum1966.graph DegreeOneSmallSpectrum1465.graph
    sourceMap1712swap fusedMap1712swap sourceMap1712swap_checked fusedMap1712swap_checked
    DegreeOneSmallComparisons.comparison1712
#print axioms sourceMap1712swap_checked
#print axioms fusedMap1712swap_checked
#print axioms certified1712swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
