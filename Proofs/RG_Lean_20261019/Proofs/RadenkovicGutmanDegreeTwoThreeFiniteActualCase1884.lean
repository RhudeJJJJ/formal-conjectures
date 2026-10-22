/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1884 : Family 10 := level10.get ⟨1336,by decide⟩
def sourceMap1884 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1884 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1884_checked : acceptsGraphIso
    (source (graph core1884) (root 10) 0 2) DegreeTwoThreeSpectrum3526.graph sourceMap1884=true := by decide +kernel
theorem fusedMap1884_checked : acceptsGraphIso
    (fused (graph core1884) (root 10) 0 2) DegreeTwoThreeSpectrum3523.graph fusedMap1884=true := by decide +kernel
theorem certified1884 : Certified (graph core1884) (root 10) 0 2 :=
  of_native_maps core1884 DegreeTwoThreeSpectrum3526.graph DegreeTwoThreeSpectrum3523.graph
    sourceMap1884 fusedMap1884 sourceMap1884_checked fusedMap1884_checked
    DegreeTwoThreeFiniteComparisons.comparison1884
#print axioms sourceMap1884_checked
#print axioms fusedMap1884_checked
#print axioms certified1884
def sourceMap1884swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1884swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1884swap_checked : acceptsGraphIso
    (source (graph core1884) (root 10) 2 0) DegreeTwoThreeSpectrum3526.graph sourceMap1884swap=true := by decide +kernel
theorem fusedMap1884swap_checked : acceptsGraphIso
    (fused (graph core1884) (root 10) 2 0) DegreeTwoThreeSpectrum3523.graph fusedMap1884swap=true := by decide +kernel
theorem certified1884swap : Certified (graph core1884) (root 10) 2 0 :=
  of_native_maps core1884 DegreeTwoThreeSpectrum3526.graph DegreeTwoThreeSpectrum3523.graph
    sourceMap1884swap fusedMap1884swap sourceMap1884swap_checked fusedMap1884swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1884
#print axioms sourceMap1884swap_checked
#print axioms fusedMap1884swap_checked
#print axioms certified1884swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
