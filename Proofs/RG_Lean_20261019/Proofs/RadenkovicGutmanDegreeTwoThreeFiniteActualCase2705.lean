/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2705 : Family 10 := level10.get ⟨833,by decide⟩
def sourceMap2705 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2705 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2705_checked : acceptsGraphIso
    (source (graph core2705) (root 10) 0 4) DegreeTwoThreeSpectrum6857.graph sourceMap2705=true := by decide +kernel
theorem fusedMap2705_checked : acceptsGraphIso
    (fused (graph core2705) (root 10) 0 4) DegreeTwoThreeSpectrum5657.graph fusedMap2705=true := by decide +kernel
theorem certified2705 : Certified (graph core2705) (root 10) 0 4 :=
  of_native_maps core2705 DegreeTwoThreeSpectrum6857.graph DegreeTwoThreeSpectrum5657.graph
    sourceMap2705 fusedMap2705 sourceMap2705_checked fusedMap2705_checked
    DegreeTwoThreeFiniteComparisons.comparison2705
#print axioms sourceMap2705_checked
#print axioms fusedMap2705_checked
#print axioms certified2705
def sourceMap2705swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2705swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2705swap_checked : acceptsGraphIso
    (source (graph core2705) (root 10) 4 0) DegreeTwoThreeSpectrum6857.graph sourceMap2705swap=true := by decide +kernel
theorem fusedMap2705swap_checked : acceptsGraphIso
    (fused (graph core2705) (root 10) 4 0) DegreeTwoThreeSpectrum5657.graph fusedMap2705swap=true := by decide +kernel
theorem certified2705swap : Certified (graph core2705) (root 10) 4 0 :=
  of_native_maps core2705 DegreeTwoThreeSpectrum6857.graph DegreeTwoThreeSpectrum5657.graph
    sourceMap2705swap fusedMap2705swap sourceMap2705swap_checked fusedMap2705swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2705
#print axioms sourceMap2705swap_checked
#print axioms fusedMap2705swap_checked
#print axioms certified2705swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
