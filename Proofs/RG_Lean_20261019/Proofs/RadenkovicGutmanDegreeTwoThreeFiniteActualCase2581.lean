/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2581 : Family 10 := level10.get ⟨477,by decide⟩
def sourceMap2581 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2581 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2581_checked : acceptsGraphIso
    (source (graph core2581) (root 10) 0 4) DegreeTwoThreeSpectrum5938.graph sourceMap2581=true := by decide +kernel
theorem fusedMap2581_checked : acceptsGraphIso
    (fused (graph core2581) (root 10) 0 4) DegreeTwoThreeSpectrum5940.graph fusedMap2581=true := by decide +kernel
theorem certified2581 : Certified (graph core2581) (root 10) 0 4 :=
  of_native_maps core2581 DegreeTwoThreeSpectrum5938.graph DegreeTwoThreeSpectrum5940.graph
    sourceMap2581 fusedMap2581 sourceMap2581_checked fusedMap2581_checked
    DegreeTwoThreeFiniteComparisons.comparison2581
#print axioms sourceMap2581_checked
#print axioms fusedMap2581_checked
#print axioms certified2581
def sourceMap2581swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2581swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2581swap_checked : acceptsGraphIso
    (source (graph core2581) (root 10) 4 0) DegreeTwoThreeSpectrum5938.graph sourceMap2581swap=true := by decide +kernel
theorem fusedMap2581swap_checked : acceptsGraphIso
    (fused (graph core2581) (root 10) 4 0) DegreeTwoThreeSpectrum5940.graph fusedMap2581swap=true := by decide +kernel
theorem certified2581swap : Certified (graph core2581) (root 10) 4 0 :=
  of_native_maps core2581 DegreeTwoThreeSpectrum5938.graph DegreeTwoThreeSpectrum5940.graph
    sourceMap2581swap fusedMap2581swap sourceMap2581swap_checked fusedMap2581swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2581
#print axioms sourceMap2581swap_checked
#print axioms fusedMap2581swap_checked
#print axioms certified2581swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
