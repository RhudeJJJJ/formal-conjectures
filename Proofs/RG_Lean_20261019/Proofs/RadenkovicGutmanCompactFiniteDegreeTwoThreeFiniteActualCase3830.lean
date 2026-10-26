/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3830 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap3830 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3830 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3830_checked : acceptsGraphIso
    (source (graph core3830) (root 8) 1 4) DegreeTwoThreeSpectrum4111.graph sourceMap3830=true := by decide +kernel
theorem fusedMap3830_checked : acceptsGraphIso
    (fused (graph core3830) (root 8) 1 4) DegreeTwoThreeSpectrum3874.graph fusedMap3830=true := by decide +kernel
theorem certified3830 : Certified (graph core3830) (root 8) 1 4 :=
  of_native_maps core3830 DegreeTwoThreeSpectrum4111.graph DegreeTwoThreeSpectrum3874.graph
    sourceMap3830 fusedMap3830 sourceMap3830_checked fusedMap3830_checked
    DegreeTwoThreeFiniteComparisons.comparison3830
#print axioms sourceMap3830_checked
#print axioms fusedMap3830_checked
#print axioms certified3830
def sourceMap3830swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3830swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3830swap_checked : acceptsGraphIso
    (source (graph core3830) (root 8) 4 1) DegreeTwoThreeSpectrum4111.graph sourceMap3830swap=true := by decide +kernel
theorem fusedMap3830swap_checked : acceptsGraphIso
    (fused (graph core3830) (root 8) 4 1) DegreeTwoThreeSpectrum3874.graph fusedMap3830swap=true := by decide +kernel
theorem certified3830swap : Certified (graph core3830) (root 8) 4 1 :=
  of_native_maps core3830 DegreeTwoThreeSpectrum4111.graph DegreeTwoThreeSpectrum3874.graph
    sourceMap3830swap fusedMap3830swap sourceMap3830swap_checked fusedMap3830swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3830
#print axioms sourceMap3830swap_checked
#print axioms fusedMap3830swap_checked
#print axioms certified3830swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
