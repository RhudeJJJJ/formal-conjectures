/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2104 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap2104 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2104 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2104_checked : acceptsGraphIso
    (source (graph core2104) (root 7) 0 4) DegreeTwoThreeSpectrum2001.graph sourceMap2104=true := by decide +kernel
theorem fusedMap2104_checked : acceptsGraphIso
    (fused (graph core2104) (root 7) 0 4) DegreeTwoThreeSpectrum1759.graph fusedMap2104=true := by decide +kernel
theorem certified2104 : Certified (graph core2104) (root 7) 0 4 :=
  of_native_maps core2104 DegreeTwoThreeSpectrum2001.graph DegreeTwoThreeSpectrum1759.graph
    sourceMap2104 fusedMap2104 sourceMap2104_checked fusedMap2104_checked
    DegreeTwoThreeFiniteComparisons.comparison2104
#print axioms sourceMap2104_checked
#print axioms fusedMap2104_checked
#print axioms certified2104
def sourceMap2104swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2104swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2104swap_checked : acceptsGraphIso
    (source (graph core2104) (root 7) 4 0) DegreeTwoThreeSpectrum2001.graph sourceMap2104swap=true := by decide +kernel
theorem fusedMap2104swap_checked : acceptsGraphIso
    (fused (graph core2104) (root 7) 4 0) DegreeTwoThreeSpectrum1759.graph fusedMap2104swap=true := by decide +kernel
theorem certified2104swap : Certified (graph core2104) (root 7) 4 0 :=
  of_native_maps core2104 DegreeTwoThreeSpectrum2001.graph DegreeTwoThreeSpectrum1759.graph
    sourceMap2104swap fusedMap2104swap sourceMap2104swap_checked fusedMap2104swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2104
#print axioms sourceMap2104swap_checked
#print axioms fusedMap2104swap_checked
#print axioms certified2104swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
