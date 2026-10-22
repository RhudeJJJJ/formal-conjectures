/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2515 : Family 10 := level10.get ⟨266,by decide⟩
def sourceMap2515 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2515 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2515_checked : acceptsGraphIso
    (source (graph core2515) (root 10) 0 4) DegreeTwoThreeSpectrum5383.graph sourceMap2515=true := by decide +kernel
theorem fusedMap2515_checked : acceptsGraphIso
    (fused (graph core2515) (root 10) 0 4) DegreeTwoThreeSpectrum5384.graph fusedMap2515=true := by decide +kernel
theorem certified2515 : Certified (graph core2515) (root 10) 0 4 :=
  of_native_maps core2515 DegreeTwoThreeSpectrum5383.graph DegreeTwoThreeSpectrum5384.graph
    sourceMap2515 fusedMap2515 sourceMap2515_checked fusedMap2515_checked
    DegreeTwoThreeFiniteComparisons.comparison2515
#print axioms sourceMap2515_checked
#print axioms fusedMap2515_checked
#print axioms certified2515
def sourceMap2515swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2515swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2515swap_checked : acceptsGraphIso
    (source (graph core2515) (root 10) 4 0) DegreeTwoThreeSpectrum5383.graph sourceMap2515swap=true := by decide +kernel
theorem fusedMap2515swap_checked : acceptsGraphIso
    (fused (graph core2515) (root 10) 4 0) DegreeTwoThreeSpectrum5384.graph fusedMap2515swap=true := by decide +kernel
theorem certified2515swap : Certified (graph core2515) (root 10) 4 0 :=
  of_native_maps core2515 DegreeTwoThreeSpectrum5383.graph DegreeTwoThreeSpectrum5384.graph
    sourceMap2515swap fusedMap2515swap sourceMap2515swap_checked fusedMap2515swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2515
#print axioms sourceMap2515swap_checked
#print axioms fusedMap2515swap_checked
#print axioms certified2515swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
