/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1779 : Family 10 := level10.get ⟨1081,by decide⟩
def sourceMap1779 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1779 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1779_checked : acceptsGraphIso
    (source (graph core1779) (root 10) 0 2) DegreeTwoThreeSpectrum3137.graph sourceMap1779=true := by decide +kernel
theorem fusedMap1779_checked : acceptsGraphIso
    (fused (graph core1779) (root 10) 0 2) DegreeTwoThreeSpectrum3141.graph fusedMap1779=true := by decide +kernel
theorem certified1779 : Certified (graph core1779) (root 10) 0 2 :=
  of_native_maps core1779 DegreeTwoThreeSpectrum3137.graph DegreeTwoThreeSpectrum3141.graph
    sourceMap1779 fusedMap1779 sourceMap1779_checked fusedMap1779_checked
    DegreeTwoThreeFiniteComparisons.comparison1779
#print axioms sourceMap1779_checked
#print axioms fusedMap1779_checked
#print axioms certified1779
def sourceMap1779swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1779swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1779swap_checked : acceptsGraphIso
    (source (graph core1779) (root 10) 2 0) DegreeTwoThreeSpectrum3137.graph sourceMap1779swap=true := by decide +kernel
theorem fusedMap1779swap_checked : acceptsGraphIso
    (fused (graph core1779) (root 10) 2 0) DegreeTwoThreeSpectrum3141.graph fusedMap1779swap=true := by decide +kernel
theorem certified1779swap : Certified (graph core1779) (root 10) 2 0 :=
  of_native_maps core1779 DegreeTwoThreeSpectrum3137.graph DegreeTwoThreeSpectrum3141.graph
    sourceMap1779swap fusedMap1779swap sourceMap1779swap_checked fusedMap1779swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1779
#print axioms sourceMap1779swap_checked
#print axioms fusedMap1779swap_checked
#print axioms certified1779swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
