/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2853 : Family 10 := level10.get ⟨1206,by decide⟩
def sourceMap2853 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2853 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2853_checked : acceptsGraphIso
    (source (graph core2853) (root 10) 0 4) DegreeTwoThreeSpectrum6386.graph sourceMap2853=true := by decide +kernel
theorem fusedMap2853_checked : acceptsGraphIso
    (fused (graph core2853) (root 10) 0 4) DegreeTwoThreeSpectrum6387.graph fusedMap2853=true := by decide +kernel
theorem certified2853 : Certified (graph core2853) (root 10) 0 4 :=
  of_native_maps core2853 DegreeTwoThreeSpectrum6386.graph DegreeTwoThreeSpectrum6387.graph
    sourceMap2853 fusedMap2853 sourceMap2853_checked fusedMap2853_checked
    DegreeTwoThreeFiniteComparisons.comparison2853
#print axioms sourceMap2853_checked
#print axioms fusedMap2853_checked
#print axioms certified2853
def sourceMap2853swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2853swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2853swap_checked : acceptsGraphIso
    (source (graph core2853) (root 10) 4 0) DegreeTwoThreeSpectrum6386.graph sourceMap2853swap=true := by decide +kernel
theorem fusedMap2853swap_checked : acceptsGraphIso
    (fused (graph core2853) (root 10) 4 0) DegreeTwoThreeSpectrum6387.graph fusedMap2853swap=true := by decide +kernel
theorem certified2853swap : Certified (graph core2853) (root 10) 4 0 :=
  of_native_maps core2853 DegreeTwoThreeSpectrum6386.graph DegreeTwoThreeSpectrum6387.graph
    sourceMap2853swap fusedMap2853swap sourceMap2853swap_checked fusedMap2853swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2853
#print axioms sourceMap2853swap_checked
#print axioms fusedMap2853swap_checked
#print axioms certified2853swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
