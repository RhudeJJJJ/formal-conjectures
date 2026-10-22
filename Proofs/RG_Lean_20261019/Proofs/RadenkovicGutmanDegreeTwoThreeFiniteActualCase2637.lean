/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2637 : Family 10 := level10.get ⟨646,by decide⟩
def sourceMap2637 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2637 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2637_checked : acceptsGraphIso
    (source (graph core2637) (root 10) 0 4) DegreeTwoThreeSpectrum6410.graph sourceMap2637=true := by decide +kernel
theorem fusedMap2637_checked : acceptsGraphIso
    (fused (graph core2637) (root 10) 0 4) DegreeTwoThreeSpectrum5344.graph fusedMap2637=true := by decide +kernel
theorem certified2637 : Certified (graph core2637) (root 10) 0 4 :=
  of_native_maps core2637 DegreeTwoThreeSpectrum6410.graph DegreeTwoThreeSpectrum5344.graph
    sourceMap2637 fusedMap2637 sourceMap2637_checked fusedMap2637_checked
    DegreeTwoThreeFiniteComparisons.comparison2637
#print axioms sourceMap2637_checked
#print axioms fusedMap2637_checked
#print axioms certified2637
def sourceMap2637swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2637swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2637swap_checked : acceptsGraphIso
    (source (graph core2637) (root 10) 4 0) DegreeTwoThreeSpectrum6410.graph sourceMap2637swap=true := by decide +kernel
theorem fusedMap2637swap_checked : acceptsGraphIso
    (fused (graph core2637) (root 10) 4 0) DegreeTwoThreeSpectrum5344.graph fusedMap2637swap=true := by decide +kernel
theorem certified2637swap : Certified (graph core2637) (root 10) 4 0 :=
  of_native_maps core2637 DegreeTwoThreeSpectrum6410.graph DegreeTwoThreeSpectrum5344.graph
    sourceMap2637swap fusedMap2637swap sourceMap2637swap_checked fusedMap2637swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2637
#print axioms sourceMap2637swap_checked
#print axioms fusedMap2637swap_checked
#print axioms certified2637swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
