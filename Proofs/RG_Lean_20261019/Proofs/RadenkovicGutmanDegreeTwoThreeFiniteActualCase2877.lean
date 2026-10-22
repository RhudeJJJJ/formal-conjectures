/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2877 : Family 10 := level10.get ⟨1265,by decide⟩
def sourceMap2877 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2877 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2877_checked : acceptsGraphIso
    (source (graph core2877) (root 10) 0 4) DegreeTwoThreeSpectrum6518.graph sourceMap2877=true := by decide +kernel
theorem fusedMap2877_checked : acceptsGraphIso
    (fused (graph core2877) (root 10) 0 4) DegreeTwoThreeSpectrum6519.graph fusedMap2877=true := by decide +kernel
theorem certified2877 : Certified (graph core2877) (root 10) 0 4 :=
  of_native_maps core2877 DegreeTwoThreeSpectrum6518.graph DegreeTwoThreeSpectrum6519.graph
    sourceMap2877 fusedMap2877 sourceMap2877_checked fusedMap2877_checked
    DegreeTwoThreeFiniteComparisons.comparison2877
#print axioms sourceMap2877_checked
#print axioms fusedMap2877_checked
#print axioms certified2877
def sourceMap2877swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2877swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2877swap_checked : acceptsGraphIso
    (source (graph core2877) (root 10) 4 0) DegreeTwoThreeSpectrum6518.graph sourceMap2877swap=true := by decide +kernel
theorem fusedMap2877swap_checked : acceptsGraphIso
    (fused (graph core2877) (root 10) 4 0) DegreeTwoThreeSpectrum6519.graph fusedMap2877swap=true := by decide +kernel
theorem certified2877swap : Certified (graph core2877) (root 10) 4 0 :=
  of_native_maps core2877 DegreeTwoThreeSpectrum6518.graph DegreeTwoThreeSpectrum6519.graph
    sourceMap2877swap fusedMap2877swap sourceMap2877swap_checked fusedMap2877swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2877
#print axioms sourceMap2877swap_checked
#print axioms fusedMap2877swap_checked
#print axioms certified2877swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
