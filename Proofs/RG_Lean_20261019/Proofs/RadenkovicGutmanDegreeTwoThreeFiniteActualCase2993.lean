/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2993 : Family 10 := level10.get ⟨1552,by decide⟩
def sourceMap2993 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2993 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2993_checked : acceptsGraphIso
    (source (graph core2993) (root 10) 0 4) DegreeTwoThreeSpectrum7089.graph sourceMap2993=true := by decide +kernel
theorem fusedMap2993_checked : acceptsGraphIso
    (fused (graph core2993) (root 10) 0 4) DegreeTwoThreeSpectrum6005.graph fusedMap2993=true := by decide +kernel
theorem certified2993 : Certified (graph core2993) (root 10) 0 4 :=
  of_native_maps core2993 DegreeTwoThreeSpectrum7089.graph DegreeTwoThreeSpectrum6005.graph
    sourceMap2993 fusedMap2993 sourceMap2993_checked fusedMap2993_checked
    DegreeTwoThreeFiniteComparisons.comparison2993
#print axioms sourceMap2993_checked
#print axioms fusedMap2993_checked
#print axioms certified2993
def sourceMap2993swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2993swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2993swap_checked : acceptsGraphIso
    (source (graph core2993) (root 10) 4 0) DegreeTwoThreeSpectrum7089.graph sourceMap2993swap=true := by decide +kernel
theorem fusedMap2993swap_checked : acceptsGraphIso
    (fused (graph core2993) (root 10) 4 0) DegreeTwoThreeSpectrum6005.graph fusedMap2993swap=true := by decide +kernel
theorem certified2993swap : Certified (graph core2993) (root 10) 4 0 :=
  of_native_maps core2993 DegreeTwoThreeSpectrum7089.graph DegreeTwoThreeSpectrum6005.graph
    sourceMap2993swap fusedMap2993swap sourceMap2993swap_checked fusedMap2993swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2993
#print axioms sourceMap2993swap_checked
#print axioms fusedMap2993swap_checked
#print axioms certified2993swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
