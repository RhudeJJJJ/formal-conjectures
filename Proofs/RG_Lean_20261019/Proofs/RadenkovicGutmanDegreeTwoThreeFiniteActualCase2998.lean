/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2998 : Family 10 := level10.get ⟨1561,by decide⟩
def sourceMap2998 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2998 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2998_checked : acceptsGraphIso
    (source (graph core2998) (root 10) 0 4) DegreeTwoThreeSpectrum7100.graph sourceMap2998=true := by decide +kernel
theorem fusedMap2998_checked : acceptsGraphIso
    (fused (graph core2998) (root 10) 0 4) DegreeTwoThreeSpectrum6025.graph fusedMap2998=true := by decide +kernel
theorem certified2998 : Certified (graph core2998) (root 10) 0 4 :=
  of_native_maps core2998 DegreeTwoThreeSpectrum7100.graph DegreeTwoThreeSpectrum6025.graph
    sourceMap2998 fusedMap2998 sourceMap2998_checked fusedMap2998_checked
    DegreeTwoThreeFiniteComparisons.comparison2998
#print axioms sourceMap2998_checked
#print axioms fusedMap2998_checked
#print axioms certified2998
def sourceMap2998swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2998swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2998swap_checked : acceptsGraphIso
    (source (graph core2998) (root 10) 4 0) DegreeTwoThreeSpectrum7100.graph sourceMap2998swap=true := by decide +kernel
theorem fusedMap2998swap_checked : acceptsGraphIso
    (fused (graph core2998) (root 10) 4 0) DegreeTwoThreeSpectrum6025.graph fusedMap2998swap=true := by decide +kernel
theorem certified2998swap : Certified (graph core2998) (root 10) 4 0 :=
  of_native_maps core2998 DegreeTwoThreeSpectrum7100.graph DegreeTwoThreeSpectrum6025.graph
    sourceMap2998swap fusedMap2998swap sourceMap2998swap_checked fusedMap2998swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2998
#print axioms sourceMap2998swap_checked
#print axioms fusedMap2998swap_checked
#print axioms certified2998swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
