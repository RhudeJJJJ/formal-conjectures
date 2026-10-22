/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2709 : Family 10 := level10.get ⟨846,by decide⟩
def sourceMap2709 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2709 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2709_checked : acceptsGraphIso
    (source (graph core2709) (root 10) 0 4) DegreeTwoThreeSpectrum6888.graph sourceMap2709=true := by decide +kernel
theorem fusedMap2709_checked : acceptsGraphIso
    (fused (graph core2709) (root 10) 0 4) DegreeTwoThreeSpectrum5678.graph fusedMap2709=true := by decide +kernel
theorem certified2709 : Certified (graph core2709) (root 10) 0 4 :=
  of_native_maps core2709 DegreeTwoThreeSpectrum6888.graph DegreeTwoThreeSpectrum5678.graph
    sourceMap2709 fusedMap2709 sourceMap2709_checked fusedMap2709_checked
    DegreeTwoThreeFiniteComparisons.comparison2709
#print axioms sourceMap2709_checked
#print axioms fusedMap2709_checked
#print axioms certified2709
def sourceMap2709swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2709swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2709swap_checked : acceptsGraphIso
    (source (graph core2709) (root 10) 4 0) DegreeTwoThreeSpectrum6888.graph sourceMap2709swap=true := by decide +kernel
theorem fusedMap2709swap_checked : acceptsGraphIso
    (fused (graph core2709) (root 10) 4 0) DegreeTwoThreeSpectrum5678.graph fusedMap2709swap=true := by decide +kernel
theorem certified2709swap : Certified (graph core2709) (root 10) 4 0 :=
  of_native_maps core2709 DegreeTwoThreeSpectrum6888.graph DegreeTwoThreeSpectrum5678.graph
    sourceMap2709swap fusedMap2709swap sourceMap2709swap_checked fusedMap2709swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2709
#print axioms sourceMap2709swap_checked
#print axioms fusedMap2709swap_checked
#print axioms certified2709swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
