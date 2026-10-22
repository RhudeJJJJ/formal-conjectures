/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1946 : Family 10 := level10.get ⟨1477,by decide⟩
def sourceMap1946 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1946 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1946_checked : acceptsGraphIso
    (source (graph core1946) (root 10) 0 2) DegreeTwoThreeSpectrum3118.graph sourceMap1946=true := by decide +kernel
theorem fusedMap1946_checked : acceptsGraphIso
    (fused (graph core1946) (root 10) 0 2) DegreeTwoThreeSpectrum3718.graph fusedMap1946=true := by decide +kernel
theorem certified1946 : Certified (graph core1946) (root 10) 0 2 :=
  of_native_maps core1946 DegreeTwoThreeSpectrum3118.graph DegreeTwoThreeSpectrum3718.graph
    sourceMap1946 fusedMap1946 sourceMap1946_checked fusedMap1946_checked
    DegreeTwoThreeFiniteComparisons.comparison1946
#print axioms sourceMap1946_checked
#print axioms fusedMap1946_checked
#print axioms certified1946
def sourceMap1946swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1946swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1946swap_checked : acceptsGraphIso
    (source (graph core1946) (root 10) 2 0) DegreeTwoThreeSpectrum3118.graph sourceMap1946swap=true := by decide +kernel
theorem fusedMap1946swap_checked : acceptsGraphIso
    (fused (graph core1946) (root 10) 2 0) DegreeTwoThreeSpectrum3718.graph fusedMap1946swap=true := by decide +kernel
theorem certified1946swap : Certified (graph core1946) (root 10) 2 0 :=
  of_native_maps core1946 DegreeTwoThreeSpectrum3118.graph DegreeTwoThreeSpectrum3718.graph
    sourceMap1946swap fusedMap1946swap sourceMap1946swap_checked fusedMap1946swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1946
#print axioms sourceMap1946swap_checked
#print axioms fusedMap1946swap_checked
#print axioms certified1946swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
