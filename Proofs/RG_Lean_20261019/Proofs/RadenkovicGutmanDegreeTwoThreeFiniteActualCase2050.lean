/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2050 : Family 10 := level10.get ⟨1804,by decide⟩
def sourceMap2050 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 0 2 v)
def fusedMap2050 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2050_checked : acceptsGraphIso
    (source (graph core2050) (root 10) 0 2) DegreeTwoThreeSpectrum3736.graph sourceMap2050=true := by decide +kernel
theorem fusedMap2050_checked : acceptsGraphIso
    (fused (graph core2050) (root 10) 0 2) DegreeTwoThreeSpectrum3737.graph fusedMap2050=true := by decide +kernel
theorem certified2050 : Certified (graph core2050) (root 10) 0 2 :=
  of_native_maps core2050 DegreeTwoThreeSpectrum3736.graph DegreeTwoThreeSpectrum3737.graph
    sourceMap2050 fusedMap2050 sourceMap2050_checked fusedMap2050_checked
    DegreeTwoThreeFiniteComparisons.comparison2050
#print axioms sourceMap2050_checked
#print axioms fusedMap2050_checked
#print axioms certified2050
def sourceMap2050swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,11] (sourceLabel 10 2 0 v)
def fusedMap2050swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2050swap_checked : acceptsGraphIso
    (source (graph core2050) (root 10) 2 0) DegreeTwoThreeSpectrum3736.graph sourceMap2050swap=true := by decide +kernel
theorem fusedMap2050swap_checked : acceptsGraphIso
    (fused (graph core2050) (root 10) 2 0) DegreeTwoThreeSpectrum3737.graph fusedMap2050swap=true := by decide +kernel
theorem certified2050swap : Certified (graph core2050) (root 10) 2 0 :=
  of_native_maps core2050 DegreeTwoThreeSpectrum3736.graph DegreeTwoThreeSpectrum3737.graph
    sourceMap2050swap fusedMap2050swap sourceMap2050swap_checked fusedMap2050swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2050
#print axioms sourceMap2050swap_checked
#print axioms fusedMap2050swap_checked
#print axioms certified2050swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
