/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2151 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap2151 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2151 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2151_checked : acceptsGraphIso
    (source (graph core2151) (root 8) 0 4) DegreeTwoThreeSpectrum2539.graph sourceMap2151=true := by decide +kernel
theorem fusedMap2151_checked : acceptsGraphIso
    (fused (graph core2151) (root 8) 0 4) DegreeTwoThreeSpectrum2541.graph fusedMap2151=true := by decide +kernel
theorem certified2151 : Certified (graph core2151) (root 8) 0 4 :=
  of_native_maps core2151 DegreeTwoThreeSpectrum2539.graph DegreeTwoThreeSpectrum2541.graph
    sourceMap2151 fusedMap2151 sourceMap2151_checked fusedMap2151_checked
    DegreeTwoThreeFiniteComparisons.comparison2151
#print axioms sourceMap2151_checked
#print axioms fusedMap2151_checked
#print axioms certified2151
def sourceMap2151swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2151swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2151swap_checked : acceptsGraphIso
    (source (graph core2151) (root 8) 4 0) DegreeTwoThreeSpectrum2539.graph sourceMap2151swap=true := by decide +kernel
theorem fusedMap2151swap_checked : acceptsGraphIso
    (fused (graph core2151) (root 8) 4 0) DegreeTwoThreeSpectrum2541.graph fusedMap2151swap=true := by decide +kernel
theorem certified2151swap : Certified (graph core2151) (root 8) 4 0 :=
  of_native_maps core2151 DegreeTwoThreeSpectrum2539.graph DegreeTwoThreeSpectrum2541.graph
    sourceMap2151swap fusedMap2151swap sourceMap2151swap_checked fusedMap2151swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2151
#print axioms sourceMap2151swap_checked
#print axioms fusedMap2151swap_checked
#print axioms certified2151swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
