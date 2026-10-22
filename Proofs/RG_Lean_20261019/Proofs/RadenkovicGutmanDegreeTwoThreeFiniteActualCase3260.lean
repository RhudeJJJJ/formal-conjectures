/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3260 : Family 9 := level9.get ⟨110,by decide⟩
def sourceMap3260 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 9 0 5 v)
def fusedMap3260 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3260_checked : acceptsGraphIso
    (source (graph core3260) (root 9) 0 5) DegreeTwoThreeSpectrum5817.graph sourceMap3260=true := by decide +kernel
theorem fusedMap3260_checked : acceptsGraphIso
    (fused (graph core3260) (root 9) 0 5) DegreeTwoThreeSpectrum5072.graph fusedMap3260=true := by decide +kernel
theorem certified3260 : Certified (graph core3260) (root 9) 0 5 :=
  of_native_maps core3260 DegreeTwoThreeSpectrum5817.graph DegreeTwoThreeSpectrum5072.graph
    sourceMap3260 fusedMap3260 sourceMap3260_checked fusedMap3260_checked
    DegreeTwoThreeFiniteComparisons.comparison3260
#print axioms sourceMap3260_checked
#print axioms fusedMap3260_checked
#print axioms certified3260
def sourceMap3260swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13,16] (sourceLabel 9 5 0 v)
def fusedMap3260swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3260swap_checked : acceptsGraphIso
    (source (graph core3260) (root 9) 5 0) DegreeTwoThreeSpectrum5817.graph sourceMap3260swap=true := by decide +kernel
theorem fusedMap3260swap_checked : acceptsGraphIso
    (fused (graph core3260) (root 9) 5 0) DegreeTwoThreeSpectrum5072.graph fusedMap3260swap=true := by decide +kernel
theorem certified3260swap : Certified (graph core3260) (root 9) 5 0 :=
  of_native_maps core3260 DegreeTwoThreeSpectrum5817.graph DegreeTwoThreeSpectrum5072.graph
    sourceMap3260swap fusedMap3260swap sourceMap3260swap_checked fusedMap3260swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3260
#print axioms sourceMap3260swap_checked
#print axioms fusedMap3260swap_checked
#print axioms certified3260swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
