/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2642 : Family 10 := level10.get ⟨660,by decide⟩
def sourceMap2642 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2642 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2642_checked : acceptsGraphIso
    (source (graph core2642) (root 10) 0 4) DegreeTwoThreeSpectrum6442.graph sourceMap2642=true := by decide +kernel
theorem fusedMap2642_checked : acceptsGraphIso
    (fused (graph core2642) (root 10) 0 4) DegreeTwoThreeSpectrum5370.graph fusedMap2642=true := by decide +kernel
theorem certified2642 : Certified (graph core2642) (root 10) 0 4 :=
  of_native_maps core2642 DegreeTwoThreeSpectrum6442.graph DegreeTwoThreeSpectrum5370.graph
    sourceMap2642 fusedMap2642 sourceMap2642_checked fusedMap2642_checked
    DegreeTwoThreeFiniteComparisons.comparison2642
#print axioms sourceMap2642_checked
#print axioms fusedMap2642_checked
#print axioms certified2642
def sourceMap2642swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2642swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2642swap_checked : acceptsGraphIso
    (source (graph core2642) (root 10) 4 0) DegreeTwoThreeSpectrum6442.graph sourceMap2642swap=true := by decide +kernel
theorem fusedMap2642swap_checked : acceptsGraphIso
    (fused (graph core2642) (root 10) 4 0) DegreeTwoThreeSpectrum5370.graph fusedMap2642swap=true := by decide +kernel
theorem certified2642swap : Certified (graph core2642) (root 10) 4 0 :=
  of_native_maps core2642 DegreeTwoThreeSpectrum6442.graph DegreeTwoThreeSpectrum5370.graph
    sourceMap2642swap fusedMap2642swap sourceMap2642swap_checked fusedMap2642swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2642
#print axioms sourceMap2642swap_checked
#print axioms fusedMap2642swap_checked
#print axioms certified2642swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
