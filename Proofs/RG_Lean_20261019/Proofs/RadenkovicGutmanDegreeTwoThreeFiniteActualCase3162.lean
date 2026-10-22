/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3162 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap3162 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3162 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3162_checked : acceptsGraphIso
    (source (graph core3162) (root 8) 0 5) DegreeTwoThreeSpectrum4135.graph sourceMap3162=true := by decide +kernel
theorem fusedMap3162_checked : acceptsGraphIso
    (fused (graph core3162) (root 8) 0 5) DegreeTwoThreeSpectrum4136.graph fusedMap3162=true := by decide +kernel
theorem certified3162 : Certified (graph core3162) (root 8) 0 5 :=
  of_native_maps core3162 DegreeTwoThreeSpectrum4135.graph DegreeTwoThreeSpectrum4136.graph
    sourceMap3162 fusedMap3162 sourceMap3162_checked fusedMap3162_checked
    DegreeTwoThreeFiniteComparisons.comparison3162
#print axioms sourceMap3162_checked
#print axioms fusedMap3162_checked
#print axioms certified3162
def sourceMap3162swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3162swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3162swap_checked : acceptsGraphIso
    (source (graph core3162) (root 8) 5 0) DegreeTwoThreeSpectrum4135.graph sourceMap3162swap=true := by decide +kernel
theorem fusedMap3162swap_checked : acceptsGraphIso
    (fused (graph core3162) (root 8) 5 0) DegreeTwoThreeSpectrum4136.graph fusedMap3162swap=true := by decide +kernel
theorem certified3162swap : Certified (graph core3162) (root 8) 5 0 :=
  of_native_maps core3162 DegreeTwoThreeSpectrum4135.graph DegreeTwoThreeSpectrum4136.graph
    sourceMap3162swap fusedMap3162swap sourceMap3162swap_checked fusedMap3162swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3162
#print axioms sourceMap3162swap_checked
#print axioms fusedMap3162swap_checked
#print axioms certified3162swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
