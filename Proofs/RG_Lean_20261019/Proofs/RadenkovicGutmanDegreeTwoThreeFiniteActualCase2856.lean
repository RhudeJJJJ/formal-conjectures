/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2856 : Family 10 := level10.get ⟨1212,by decide⟩
def sourceMap2856 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2856 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2856_checked : acceptsGraphIso
    (source (graph core2856) (root 10) 0 4) DegreeTwoThreeSpectrum6398.graph sourceMap2856=true := by decide +kernel
theorem fusedMap2856_checked : acceptsGraphIso
    (fused (graph core2856) (root 10) 0 4) DegreeTwoThreeSpectrum6399.graph fusedMap2856=true := by decide +kernel
theorem certified2856 : Certified (graph core2856) (root 10) 0 4 :=
  of_native_maps core2856 DegreeTwoThreeSpectrum6398.graph DegreeTwoThreeSpectrum6399.graph
    sourceMap2856 fusedMap2856 sourceMap2856_checked fusedMap2856_checked
    DegreeTwoThreeFiniteComparisons.comparison2856
#print axioms sourceMap2856_checked
#print axioms fusedMap2856_checked
#print axioms certified2856
def sourceMap2856swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2856swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2856swap_checked : acceptsGraphIso
    (source (graph core2856) (root 10) 4 0) DegreeTwoThreeSpectrum6398.graph sourceMap2856swap=true := by decide +kernel
theorem fusedMap2856swap_checked : acceptsGraphIso
    (fused (graph core2856) (root 10) 4 0) DegreeTwoThreeSpectrum6399.graph fusedMap2856swap=true := by decide +kernel
theorem certified2856swap : Certified (graph core2856) (root 10) 4 0 :=
  of_native_maps core2856 DegreeTwoThreeSpectrum6398.graph DegreeTwoThreeSpectrum6399.graph
    sourceMap2856swap fusedMap2856swap sourceMap2856swap_checked fusedMap2856swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2856
#print axioms sourceMap2856swap_checked
#print axioms fusedMap2856swap_checked
#print axioms certified2856swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
