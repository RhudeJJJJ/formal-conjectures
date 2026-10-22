/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2879 : Family 10 := level10.get ⟨1271,by decide⟩
def sourceMap2879 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2879 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2879_checked : acceptsGraphIso
    (source (graph core2879) (root 10) 0 4) DegreeTwoThreeSpectrum6532.graph sourceMap2879=true := by decide +kernel
theorem fusedMap2879_checked : acceptsGraphIso
    (fused (graph core2879) (root 10) 0 4) DegreeTwoThreeSpectrum6533.graph fusedMap2879=true := by decide +kernel
theorem certified2879 : Certified (graph core2879) (root 10) 0 4 :=
  of_native_maps core2879 DegreeTwoThreeSpectrum6532.graph DegreeTwoThreeSpectrum6533.graph
    sourceMap2879 fusedMap2879 sourceMap2879_checked fusedMap2879_checked
    DegreeTwoThreeFiniteComparisons.comparison2879
#print axioms sourceMap2879_checked
#print axioms fusedMap2879_checked
#print axioms certified2879
def sourceMap2879swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2879swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2879swap_checked : acceptsGraphIso
    (source (graph core2879) (root 10) 4 0) DegreeTwoThreeSpectrum6532.graph sourceMap2879swap=true := by decide +kernel
theorem fusedMap2879swap_checked : acceptsGraphIso
    (fused (graph core2879) (root 10) 4 0) DegreeTwoThreeSpectrum6533.graph fusedMap2879swap=true := by decide +kernel
theorem certified2879swap : Certified (graph core2879) (root 10) 4 0 :=
  of_native_maps core2879 DegreeTwoThreeSpectrum6532.graph DegreeTwoThreeSpectrum6533.graph
    sourceMap2879swap fusedMap2879swap sourceMap2879swap_checked fusedMap2879swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2879
#print axioms sourceMap2879swap_checked
#print axioms fusedMap2879swap_checked
#print axioms certified2879swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
