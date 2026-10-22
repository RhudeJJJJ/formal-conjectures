/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2228 : Family 9 := level9.get ⟨67,by decide⟩
def sourceMap2228 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2228 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 0 4 v)
theorem sourceMap2228_checked : acceptsGraphIso
    (source (graph core2228) (root 9) 0 4) DegreeTwoThreeSpectrum3978.graph sourceMap2228=true := by decide +kernel
theorem fusedMap2228_checked : acceptsGraphIso
    (fused (graph core2228) (root 9) 0 4) DegreeTwoThreeSpectrum3980.graph fusedMap2228=true := by decide +kernel
theorem certified2228 : Certified (graph core2228) (root 9) 0 4 :=
  of_native_maps core2228 DegreeTwoThreeSpectrum3978.graph DegreeTwoThreeSpectrum3980.graph
    sourceMap2228 fusedMap2228 sourceMap2228_checked fusedMap2228_checked
    DegreeTwoThreeFiniteComparisons.comparison2228
#print axioms sourceMap2228_checked
#print axioms fusedMap2228_checked
#print axioms certified2228
def sourceMap2228swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2228swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 4 0 v)
theorem sourceMap2228swap_checked : acceptsGraphIso
    (source (graph core2228) (root 9) 4 0) DegreeTwoThreeSpectrum3978.graph sourceMap2228swap=true := by decide +kernel
theorem fusedMap2228swap_checked : acceptsGraphIso
    (fused (graph core2228) (root 9) 4 0) DegreeTwoThreeSpectrum3980.graph fusedMap2228swap=true := by decide +kernel
theorem certified2228swap : Certified (graph core2228) (root 9) 4 0 :=
  of_native_maps core2228 DegreeTwoThreeSpectrum3978.graph DegreeTwoThreeSpectrum3980.graph
    sourceMap2228swap fusedMap2228swap sourceMap2228swap_checked fusedMap2228swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2228
#print axioms sourceMap2228swap_checked
#print axioms fusedMap2228swap_checked
#print axioms certified2228swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
