/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2977 : Family 10 := level10.get ⟨1498,by decide⟩
def sourceMap2977 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2977 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2977_checked : acceptsGraphIso
    (source (graph core2977) (root 10) 0 4) DegreeTwoThreeSpectrum7002.graph sourceMap2977=true := by decide +kernel
theorem fusedMap2977_checked : acceptsGraphIso
    (fused (graph core2977) (root 10) 0 4) DegreeTwoThreeSpectrum7003.graph fusedMap2977=true := by decide +kernel
theorem certified2977 : Certified (graph core2977) (root 10) 0 4 :=
  of_native_maps core2977 DegreeTwoThreeSpectrum7002.graph DegreeTwoThreeSpectrum7003.graph
    sourceMap2977 fusedMap2977 sourceMap2977_checked fusedMap2977_checked
    DegreeTwoThreeFiniteComparisons.comparison2977
#print axioms sourceMap2977_checked
#print axioms fusedMap2977_checked
#print axioms certified2977
def sourceMap2977swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2977swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2977swap_checked : acceptsGraphIso
    (source (graph core2977) (root 10) 4 0) DegreeTwoThreeSpectrum7002.graph sourceMap2977swap=true := by decide +kernel
theorem fusedMap2977swap_checked : acceptsGraphIso
    (fused (graph core2977) (root 10) 4 0) DegreeTwoThreeSpectrum7003.graph fusedMap2977swap=true := by decide +kernel
theorem certified2977swap : Certified (graph core2977) (root 10) 4 0 :=
  of_native_maps core2977 DegreeTwoThreeSpectrum7002.graph DegreeTwoThreeSpectrum7003.graph
    sourceMap2977swap fusedMap2977swap sourceMap2977swap_checked fusedMap2977swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2977
#print axioms sourceMap2977swap_checked
#print axioms fusedMap2977swap_checked
#print axioms certified2977swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
