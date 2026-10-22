/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1360 : Family 9 := level9.get ⟨503,by decide⟩
def sourceMap1360 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,4,5,6,1,2,3] (sourceLabel 9 0 2 v)
def fusedMap1360 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1360_checked : acceptsGraphIso
    (source (graph core1360) (root 9) 0 2) DegreeTwoThreeSpectrum2208.graph sourceMap1360=true := by decide +kernel
theorem fusedMap1360_checked : acceptsGraphIso
    (fused (graph core1360) (root 9) 0 2) DegreeTwoThreeSpectrum2213.graph fusedMap1360=true := by decide +kernel
theorem certified1360 : Certified (graph core1360) (root 9) 0 2 :=
  of_native_maps core1360 DegreeTwoThreeSpectrum2208.graph DegreeTwoThreeSpectrum2213.graph
    sourceMap1360 fusedMap1360 sourceMap1360_checked fusedMap1360_checked
    DegreeTwoThreeFiniteComparisons.comparison1360
#print axioms sourceMap1360_checked
#print axioms fusedMap1360_checked
#print axioms certified1360
def sourceMap1360swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,4,5,1,2,3,6] (sourceLabel 9 2 0 v)
def fusedMap1360swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1360swap_checked : acceptsGraphIso
    (source (graph core1360) (root 9) 2 0) DegreeTwoThreeSpectrum2208.graph sourceMap1360swap=true := by decide +kernel
theorem fusedMap1360swap_checked : acceptsGraphIso
    (fused (graph core1360) (root 9) 2 0) DegreeTwoThreeSpectrum2213.graph fusedMap1360swap=true := by decide +kernel
theorem certified1360swap : Certified (graph core1360) (root 9) 2 0 :=
  of_native_maps core1360 DegreeTwoThreeSpectrum2208.graph DegreeTwoThreeSpectrum2213.graph
    sourceMap1360swap fusedMap1360swap sourceMap1360swap_checked fusedMap1360swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1360
#print axioms sourceMap1360swap_checked
#print axioms fusedMap1360swap_checked
#print axioms certified1360swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
