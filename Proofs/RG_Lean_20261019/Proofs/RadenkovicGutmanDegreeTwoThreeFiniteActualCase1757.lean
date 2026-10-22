/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1757 : Family 10 := level10.get ⟨1025,by decide⟩
def sourceMap1757 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1757 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1757_checked : acceptsGraphIso
    (source (graph core1757) (root 10) 0 2) DegreeTwoThreeSpectrum3048.graph sourceMap1757=true := by decide +kernel
theorem fusedMap1757_checked : acceptsGraphIso
    (fused (graph core1757) (root 10) 0 2) DegreeTwoThreeSpectrum3049.graph fusedMap1757=true := by decide +kernel
theorem certified1757 : Certified (graph core1757) (root 10) 0 2 :=
  of_native_maps core1757 DegreeTwoThreeSpectrum3048.graph DegreeTwoThreeSpectrum3049.graph
    sourceMap1757 fusedMap1757 sourceMap1757_checked fusedMap1757_checked
    DegreeTwoThreeFiniteComparisons.comparison1757
#print axioms sourceMap1757_checked
#print axioms fusedMap1757_checked
#print axioms certified1757
def sourceMap1757swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1757swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1757swap_checked : acceptsGraphIso
    (source (graph core1757) (root 10) 2 0) DegreeTwoThreeSpectrum3048.graph sourceMap1757swap=true := by decide +kernel
theorem fusedMap1757swap_checked : acceptsGraphIso
    (fused (graph core1757) (root 10) 2 0) DegreeTwoThreeSpectrum3049.graph fusedMap1757swap=true := by decide +kernel
theorem certified1757swap : Certified (graph core1757) (root 10) 2 0 :=
  of_native_maps core1757 DegreeTwoThreeSpectrum3048.graph DegreeTwoThreeSpectrum3049.graph
    sourceMap1757swap fusedMap1757swap sourceMap1757swap_checked fusedMap1757swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1757
#print axioms sourceMap1757swap_checked
#print axioms fusedMap1757swap_checked
#print axioms certified1757swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
