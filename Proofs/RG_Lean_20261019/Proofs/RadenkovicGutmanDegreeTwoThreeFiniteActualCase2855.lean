/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2855 : Family 10 := level10.get ⟨1209,by decide⟩
def sourceMap2855 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2855 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2855_checked : acceptsGraphIso
    (source (graph core2855) (root 10) 0 4) DegreeTwoThreeSpectrum6392.graph sourceMap2855=true := by decide +kernel
theorem fusedMap2855_checked : acceptsGraphIso
    (fused (graph core2855) (root 10) 0 4) DegreeTwoThreeSpectrum6393.graph fusedMap2855=true := by decide +kernel
theorem certified2855 : Certified (graph core2855) (root 10) 0 4 :=
  of_native_maps core2855 DegreeTwoThreeSpectrum6392.graph DegreeTwoThreeSpectrum6393.graph
    sourceMap2855 fusedMap2855 sourceMap2855_checked fusedMap2855_checked
    DegreeTwoThreeFiniteComparisons.comparison2855
#print axioms sourceMap2855_checked
#print axioms fusedMap2855_checked
#print axioms certified2855
def sourceMap2855swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2855swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2855swap_checked : acceptsGraphIso
    (source (graph core2855) (root 10) 4 0) DegreeTwoThreeSpectrum6392.graph sourceMap2855swap=true := by decide +kernel
theorem fusedMap2855swap_checked : acceptsGraphIso
    (fused (graph core2855) (root 10) 4 0) DegreeTwoThreeSpectrum6393.graph fusedMap2855swap=true := by decide +kernel
theorem certified2855swap : Certified (graph core2855) (root 10) 4 0 :=
  of_native_maps core2855 DegreeTwoThreeSpectrum6392.graph DegreeTwoThreeSpectrum6393.graph
    sourceMap2855swap fusedMap2855swap sourceMap2855swap_checked fusedMap2855swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2855
#print axioms sourceMap2855swap_checked
#print axioms fusedMap2855swap_checked
#print axioms certified2855swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
