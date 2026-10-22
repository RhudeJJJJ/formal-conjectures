/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1761 : Family 10 := level10.get ⟨1035,by decide⟩
def sourceMap1761 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1761 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1761_checked : acceptsGraphIso
    (source (graph core1761) (root 10) 0 2) DegreeTwoThreeSpectrum3066.graph sourceMap1761=true := by decide +kernel
theorem fusedMap1761_checked : acceptsGraphIso
    (fused (graph core1761) (root 10) 0 2) DegreeTwoThreeSpectrum3067.graph fusedMap1761=true := by decide +kernel
theorem certified1761 : Certified (graph core1761) (root 10) 0 2 :=
  of_native_maps core1761 DegreeTwoThreeSpectrum3066.graph DegreeTwoThreeSpectrum3067.graph
    sourceMap1761 fusedMap1761 sourceMap1761_checked fusedMap1761_checked
    DegreeTwoThreeFiniteComparisons.comparison1761
#print axioms sourceMap1761_checked
#print axioms fusedMap1761_checked
#print axioms certified1761
def sourceMap1761swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1761swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1761swap_checked : acceptsGraphIso
    (source (graph core1761) (root 10) 2 0) DegreeTwoThreeSpectrum3066.graph sourceMap1761swap=true := by decide +kernel
theorem fusedMap1761swap_checked : acceptsGraphIso
    (fused (graph core1761) (root 10) 2 0) DegreeTwoThreeSpectrum3067.graph fusedMap1761swap=true := by decide +kernel
theorem certified1761swap : Certified (graph core1761) (root 10) 2 0 :=
  of_native_maps core1761 DegreeTwoThreeSpectrum3066.graph DegreeTwoThreeSpectrum3067.graph
    sourceMap1761swap fusedMap1761swap sourceMap1761swap_checked fusedMap1761swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1761
#print axioms sourceMap1761swap_checked
#print axioms fusedMap1761swap_checked
#print axioms certified1761swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
