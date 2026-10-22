/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2835 : Family 10 := level10.get ⟨1163,by decide⟩
def sourceMap2835 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2835 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2835_checked : acceptsGraphIso
    (source (graph core2835) (root 10) 0 4) DegreeTwoThreeSpectrum6309.graph sourceMap2835=true := by decide +kernel
theorem fusedMap2835_checked : acceptsGraphIso
    (fused (graph core2835) (root 10) 0 4) DegreeTwoThreeSpectrum6310.graph fusedMap2835=true := by decide +kernel
theorem certified2835 : Certified (graph core2835) (root 10) 0 4 :=
  of_native_maps core2835 DegreeTwoThreeSpectrum6309.graph DegreeTwoThreeSpectrum6310.graph
    sourceMap2835 fusedMap2835 sourceMap2835_checked fusedMap2835_checked
    DegreeTwoThreeFiniteComparisons.comparison2835
#print axioms sourceMap2835_checked
#print axioms fusedMap2835_checked
#print axioms certified2835
def sourceMap2835swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2835swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2835swap_checked : acceptsGraphIso
    (source (graph core2835) (root 10) 4 0) DegreeTwoThreeSpectrum6309.graph sourceMap2835swap=true := by decide +kernel
theorem fusedMap2835swap_checked : acceptsGraphIso
    (fused (graph core2835) (root 10) 4 0) DegreeTwoThreeSpectrum6310.graph fusedMap2835swap=true := by decide +kernel
theorem certified2835swap : Certified (graph core2835) (root 10) 4 0 :=
  of_native_maps core2835 DegreeTwoThreeSpectrum6309.graph DegreeTwoThreeSpectrum6310.graph
    sourceMap2835swap fusedMap2835swap sourceMap2835swap_checked fusedMap2835swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2835
#print axioms sourceMap2835swap_checked
#print axioms fusedMap2835swap_checked
#print axioms certified2835swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
