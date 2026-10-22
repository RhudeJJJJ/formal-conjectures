/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1782 : Family 10 := level10.get ⟨1086,by decide⟩
def sourceMap1782 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1782 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1782_checked : acceptsGraphIso
    (source (graph core1782) (root 10) 0 2) DegreeTwoThreeSpectrum3143.graph sourceMap1782=true := by decide +kernel
theorem fusedMap1782_checked : acceptsGraphIso
    (fused (graph core1782) (root 10) 0 2) DegreeTwoThreeSpectrum3153.graph fusedMap1782=true := by decide +kernel
theorem certified1782 : Certified (graph core1782) (root 10) 0 2 :=
  of_native_maps core1782 DegreeTwoThreeSpectrum3143.graph DegreeTwoThreeSpectrum3153.graph
    sourceMap1782 fusedMap1782 sourceMap1782_checked fusedMap1782_checked
    DegreeTwoThreeFiniteComparisons.comparison1782
#print axioms sourceMap1782_checked
#print axioms fusedMap1782_checked
#print axioms certified1782
def sourceMap1782swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1782swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1782swap_checked : acceptsGraphIso
    (source (graph core1782) (root 10) 2 0) DegreeTwoThreeSpectrum3143.graph sourceMap1782swap=true := by decide +kernel
theorem fusedMap1782swap_checked : acceptsGraphIso
    (fused (graph core1782) (root 10) 2 0) DegreeTwoThreeSpectrum3153.graph fusedMap1782swap=true := by decide +kernel
theorem certified1782swap : Certified (graph core1782) (root 10) 2 0 :=
  of_native_maps core1782 DegreeTwoThreeSpectrum3143.graph DegreeTwoThreeSpectrum3153.graph
    sourceMap1782swap fusedMap1782swap sourceMap1782swap_checked fusedMap1782swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1782
#print axioms sourceMap1782swap_checked
#print axioms fusedMap1782swap_checked
#print axioms certified1782swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
