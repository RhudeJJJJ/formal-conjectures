/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3877 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap3877 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3877 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3877_checked : acceptsGraphIso
    (source (graph core3877) (root 8) 1 4) DegreeTwoThreeSpectrum4558.graph sourceMap3877=true := by decide +kernel
theorem fusedMap3877_checked : acceptsGraphIso
    (fused (graph core3877) (root 8) 1 4) DegreeTwoThreeSpectrum4060.graph fusedMap3877=true := by decide +kernel
theorem certified3877 : Certified (graph core3877) (root 8) 1 4 :=
  of_native_maps core3877 DegreeTwoThreeSpectrum4558.graph DegreeTwoThreeSpectrum4060.graph
    sourceMap3877 fusedMap3877 sourceMap3877_checked fusedMap3877_checked
    DegreeTwoThreeFiniteComparisons.comparison3877
#print axioms sourceMap3877_checked
#print axioms fusedMap3877_checked
#print axioms certified3877
def sourceMap3877swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3877swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3877swap_checked : acceptsGraphIso
    (source (graph core3877) (root 8) 4 1) DegreeTwoThreeSpectrum4558.graph sourceMap3877swap=true := by decide +kernel
theorem fusedMap3877swap_checked : acceptsGraphIso
    (fused (graph core3877) (root 8) 4 1) DegreeTwoThreeSpectrum4060.graph fusedMap3877swap=true := by decide +kernel
theorem certified3877swap : Certified (graph core3877) (root 8) 4 1 :=
  of_native_maps core3877 DegreeTwoThreeSpectrum4558.graph DegreeTwoThreeSpectrum4060.graph
    sourceMap3877swap fusedMap3877swap sourceMap3877swap_checked fusedMap3877swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3877
#print axioms sourceMap3877swap_checked
#print axioms fusedMap3877swap_checked
#print axioms certified3877swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
