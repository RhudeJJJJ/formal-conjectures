/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3183 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap3183 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3183 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3183_checked : acceptsGraphIso
    (source (graph core3183) (root 8) 0 5) DegreeTwoThreeSpectrum4470.graph sourceMap3183=true := by decide +kernel
theorem fusedMap3183_checked : acceptsGraphIso
    (fused (graph core3183) (root 8) 0 5) DegreeTwoThreeSpectrum4006.graph fusedMap3183=true := by decide +kernel
theorem certified3183 : Certified (graph core3183) (root 8) 0 5 :=
  of_native_maps core3183 DegreeTwoThreeSpectrum4470.graph DegreeTwoThreeSpectrum4006.graph
    sourceMap3183 fusedMap3183 sourceMap3183_checked fusedMap3183_checked
    DegreeTwoThreeFiniteComparisons.comparison3183
#print axioms sourceMap3183_checked
#print axioms fusedMap3183_checked
#print axioms certified3183
def sourceMap3183swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3183swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3183swap_checked : acceptsGraphIso
    (source (graph core3183) (root 8) 5 0) DegreeTwoThreeSpectrum4470.graph sourceMap3183swap=true := by decide +kernel
theorem fusedMap3183swap_checked : acceptsGraphIso
    (fused (graph core3183) (root 8) 5 0) DegreeTwoThreeSpectrum4006.graph fusedMap3183swap=true := by decide +kernel
theorem certified3183swap : Certified (graph core3183) (root 8) 5 0 :=
  of_native_maps core3183 DegreeTwoThreeSpectrum4470.graph DegreeTwoThreeSpectrum4006.graph
    sourceMap3183swap fusedMap3183swap sourceMap3183swap_checked fusedMap3183swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3183
#print axioms sourceMap3183swap_checked
#print axioms fusedMap3183swap_checked
#print axioms certified3183swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
