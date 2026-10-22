/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2850 : Family 10 := level10.get ⟨1200,by decide⟩
def sourceMap2850 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2850 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2850_checked : acceptsGraphIso
    (source (graph core2850) (root 10) 0 4) DegreeTwoThreeSpectrum6376.graph sourceMap2850=true := by decide +kernel
theorem fusedMap2850_checked : acceptsGraphIso
    (fused (graph core2850) (root 10) 0 4) DegreeTwoThreeSpectrum6377.graph fusedMap2850=true := by decide +kernel
theorem certified2850 : Certified (graph core2850) (root 10) 0 4 :=
  of_native_maps core2850 DegreeTwoThreeSpectrum6376.graph DegreeTwoThreeSpectrum6377.graph
    sourceMap2850 fusedMap2850 sourceMap2850_checked fusedMap2850_checked
    DegreeTwoThreeFiniteComparisons.comparison2850
#print axioms sourceMap2850_checked
#print axioms fusedMap2850_checked
#print axioms certified2850
def sourceMap2850swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2850swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2850swap_checked : acceptsGraphIso
    (source (graph core2850) (root 10) 4 0) DegreeTwoThreeSpectrum6376.graph sourceMap2850swap=true := by decide +kernel
theorem fusedMap2850swap_checked : acceptsGraphIso
    (fused (graph core2850) (root 10) 4 0) DegreeTwoThreeSpectrum6377.graph fusedMap2850swap=true := by decide +kernel
theorem certified2850swap : Certified (graph core2850) (root 10) 4 0 :=
  of_native_maps core2850 DegreeTwoThreeSpectrum6376.graph DegreeTwoThreeSpectrum6377.graph
    sourceMap2850swap fusedMap2850swap sourceMap2850swap_checked fusedMap2850swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2850
#print axioms sourceMap2850swap_checked
#print axioms fusedMap2850swap_checked
#print axioms certified2850swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
