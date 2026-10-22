/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1225 : Family 9 := level9.get ⟨134,by decide⟩
def sourceMap1225 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,5,6,7,8,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1225 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,6,7,8,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1225_checked : acceptsGraphIso
    (source (graph core1225) (root 9) 0 2) DegreeTwoThreeSpectrum1863.graph sourceMap1225=true := by decide +kernel
theorem fusedMap1225_checked : acceptsGraphIso
    (fused (graph core1225) (root 9) 0 2) DegreeTwoThreeSpectrum1911.graph fusedMap1225=true := by decide +kernel
theorem certified1225 : Certified (graph core1225) (root 9) 0 2 :=
  of_native_maps core1225 DegreeTwoThreeSpectrum1863.graph DegreeTwoThreeSpectrum1911.graph
    sourceMap1225 fusedMap1225 sourceMap1225_checked fusedMap1225_checked
    DegreeTwoThreeFiniteComparisons.comparison1225
#print axioms sourceMap1225_checked
#print axioms fusedMap1225_checked
#print axioms certified1225
def sourceMap1225swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,5,6,7,2,3,4,8] (sourceLabel 9 2 0 v)
def fusedMap1225swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,6,7,8,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1225swap_checked : acceptsGraphIso
    (source (graph core1225) (root 9) 2 0) DegreeTwoThreeSpectrum1863.graph sourceMap1225swap=true := by decide +kernel
theorem fusedMap1225swap_checked : acceptsGraphIso
    (fused (graph core1225) (root 9) 2 0) DegreeTwoThreeSpectrum1911.graph fusedMap1225swap=true := by decide +kernel
theorem certified1225swap : Certified (graph core1225) (root 9) 2 0 :=
  of_native_maps core1225 DegreeTwoThreeSpectrum1863.graph DegreeTwoThreeSpectrum1911.graph
    sourceMap1225swap fusedMap1225swap sourceMap1225swap_checked fusedMap1225swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1225
#print axioms sourceMap1225swap_checked
#print axioms fusedMap1225swap_checked
#print axioms certified1225swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
