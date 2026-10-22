/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2112 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap2112 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2112 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2112_checked : acceptsGraphIso
    (source (graph core2112) (root 7) 0 4) DegreeTwoThreeSpectrum2127.graph sourceMap2112=true := by decide +kernel
theorem fusedMap2112_checked : acceptsGraphIso
    (fused (graph core2112) (root 7) 0 4) DegreeTwoThreeSpectrum1820.graph fusedMap2112=true := by decide +kernel
theorem certified2112 : Certified (graph core2112) (root 7) 0 4 :=
  of_native_maps core2112 DegreeTwoThreeSpectrum2127.graph DegreeTwoThreeSpectrum1820.graph
    sourceMap2112 fusedMap2112 sourceMap2112_checked fusedMap2112_checked
    DegreeTwoThreeFiniteComparisons.comparison2112
#print axioms sourceMap2112_checked
#print axioms fusedMap2112_checked
#print axioms certified2112
def sourceMap2112swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2112swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2112swap_checked : acceptsGraphIso
    (source (graph core2112) (root 7) 4 0) DegreeTwoThreeSpectrum2127.graph sourceMap2112swap=true := by decide +kernel
theorem fusedMap2112swap_checked : acceptsGraphIso
    (fused (graph core2112) (root 7) 4 0) DegreeTwoThreeSpectrum1820.graph fusedMap2112swap=true := by decide +kernel
theorem certified2112swap : Certified (graph core2112) (root 7) 4 0 :=
  of_native_maps core2112 DegreeTwoThreeSpectrum2127.graph DegreeTwoThreeSpectrum1820.graph
    sourceMap2112swap fusedMap2112swap sourceMap2112swap_checked fusedMap2112swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2112
#print axioms sourceMap2112swap_checked
#print axioms fusedMap2112swap_checked
#print axioms certified2112swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
