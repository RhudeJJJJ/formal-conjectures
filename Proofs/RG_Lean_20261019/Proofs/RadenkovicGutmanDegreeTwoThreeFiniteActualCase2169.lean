/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2169 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap2169 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2169 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2169_checked : acceptsGraphIso
    (source (graph core2169) (root 8) 0 4) DegreeTwoThreeSpectrum2820.graph sourceMap2169=true := by decide +kernel
theorem fusedMap2169_checked : acceptsGraphIso
    (fused (graph core2169) (root 8) 0 4) DegreeTwoThreeSpectrum2822.graph fusedMap2169=true := by decide +kernel
theorem certified2169 : Certified (graph core2169) (root 8) 0 4 :=
  of_native_maps core2169 DegreeTwoThreeSpectrum2820.graph DegreeTwoThreeSpectrum2822.graph
    sourceMap2169 fusedMap2169 sourceMap2169_checked fusedMap2169_checked
    DegreeTwoThreeFiniteComparisons.comparison2169
#print axioms sourceMap2169_checked
#print axioms fusedMap2169_checked
#print axioms certified2169
def sourceMap2169swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2169swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2169swap_checked : acceptsGraphIso
    (source (graph core2169) (root 8) 4 0) DegreeTwoThreeSpectrum2820.graph sourceMap2169swap=true := by decide +kernel
theorem fusedMap2169swap_checked : acceptsGraphIso
    (fused (graph core2169) (root 8) 4 0) DegreeTwoThreeSpectrum2822.graph fusedMap2169swap=true := by decide +kernel
theorem certified2169swap : Certified (graph core2169) (root 8) 4 0 :=
  of_native_maps core2169 DegreeTwoThreeSpectrum2820.graph DegreeTwoThreeSpectrum2822.graph
    sourceMap2169swap fusedMap2169swap sourceMap2169swap_checked fusedMap2169swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2169
#print axioms sourceMap2169swap_checked
#print axioms fusedMap2169swap_checked
#print axioms certified2169swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
