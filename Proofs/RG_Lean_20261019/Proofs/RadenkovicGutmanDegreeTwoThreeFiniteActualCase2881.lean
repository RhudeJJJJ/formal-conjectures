/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2881 : Family 10 := level10.get ⟨1277,by decide⟩
def sourceMap2881 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2881 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2881_checked : acceptsGraphIso
    (source (graph core2881) (root 10) 0 4) DegreeTwoThreeSpectrum6540.graph sourceMap2881=true := by decide +kernel
theorem fusedMap2881_checked : acceptsGraphIso
    (fused (graph core2881) (root 10) 0 4) DegreeTwoThreeSpectrum6541.graph fusedMap2881=true := by decide +kernel
theorem certified2881 : Certified (graph core2881) (root 10) 0 4 :=
  of_native_maps core2881 DegreeTwoThreeSpectrum6540.graph DegreeTwoThreeSpectrum6541.graph
    sourceMap2881 fusedMap2881 sourceMap2881_checked fusedMap2881_checked
    DegreeTwoThreeFiniteComparisons.comparison2881
#print axioms sourceMap2881_checked
#print axioms fusedMap2881_checked
#print axioms certified2881
def sourceMap2881swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2881swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2881swap_checked : acceptsGraphIso
    (source (graph core2881) (root 10) 4 0) DegreeTwoThreeSpectrum6540.graph sourceMap2881swap=true := by decide +kernel
theorem fusedMap2881swap_checked : acceptsGraphIso
    (fused (graph core2881) (root 10) 4 0) DegreeTwoThreeSpectrum6541.graph fusedMap2881swap=true := by decide +kernel
theorem certified2881swap : Certified (graph core2881) (root 10) 4 0 :=
  of_native_maps core2881 DegreeTwoThreeSpectrum6540.graph DegreeTwoThreeSpectrum6541.graph
    sourceMap2881swap fusedMap2881swap sourceMap2881swap_checked fusedMap2881swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2881
#print axioms sourceMap2881swap_checked
#print axioms fusedMap2881swap_checked
#print axioms certified2881swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
