/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2747 : Family 10 := level10.get ⟨945,by decide⟩
def sourceMap2747 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2747 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2747_checked : acceptsGraphIso
    (source (graph core2747) (root 10) 0 4) DegreeTwoThreeSpectrum7025.graph sourceMap2747=true := by decide +kernel
theorem fusedMap2747_checked : acceptsGraphIso
    (fused (graph core2747) (root 10) 0 4) DegreeTwoThreeSpectrum5843.graph fusedMap2747=true := by decide +kernel
theorem certified2747 : Certified (graph core2747) (root 10) 0 4 :=
  of_native_maps core2747 DegreeTwoThreeSpectrum7025.graph DegreeTwoThreeSpectrum5843.graph
    sourceMap2747 fusedMap2747 sourceMap2747_checked fusedMap2747_checked
    DegreeTwoThreeFiniteComparisons.comparison2747
#print axioms sourceMap2747_checked
#print axioms fusedMap2747_checked
#print axioms certified2747
def sourceMap2747swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2747swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2747swap_checked : acceptsGraphIso
    (source (graph core2747) (root 10) 4 0) DegreeTwoThreeSpectrum7025.graph sourceMap2747swap=true := by decide +kernel
theorem fusedMap2747swap_checked : acceptsGraphIso
    (fused (graph core2747) (root 10) 4 0) DegreeTwoThreeSpectrum5843.graph fusedMap2747swap=true := by decide +kernel
theorem certified2747swap : Certified (graph core2747) (root 10) 4 0 :=
  of_native_maps core2747 DegreeTwoThreeSpectrum7025.graph DegreeTwoThreeSpectrum5843.graph
    sourceMap2747swap fusedMap2747swap sourceMap2747swap_checked fusedMap2747swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2747
#print axioms sourceMap2747swap_checked
#print axioms fusedMap2747swap_checked
#print axioms certified2747swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
