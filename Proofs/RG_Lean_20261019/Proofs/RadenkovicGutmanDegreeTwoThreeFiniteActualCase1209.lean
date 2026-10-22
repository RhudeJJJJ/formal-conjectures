/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1209 : Family 9 := level9.get ⟨87,by decide⟩
def sourceMap1209 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1209 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1209_checked : acceptsGraphIso
    (source (graph core1209) (root 9) 0 2) DegreeTwoThreeSpectrum1848.graph sourceMap1209=true := by decide +kernel
theorem fusedMap1209_checked : acceptsGraphIso
    (fused (graph core1209) (root 9) 0 2) DegreeTwoThreeSpectrum1850.graph fusedMap1209=true := by decide +kernel
theorem certified1209 : Certified (graph core1209) (root 9) 0 2 :=
  of_native_maps core1209 DegreeTwoThreeSpectrum1848.graph DegreeTwoThreeSpectrum1850.graph
    sourceMap1209 fusedMap1209 sourceMap1209_checked fusedMap1209_checked
    DegreeTwoThreeFiniteComparisons.comparison1209
#print axioms sourceMap1209_checked
#print axioms fusedMap1209_checked
#print axioms certified1209
def sourceMap1209swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1209swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1209swap_checked : acceptsGraphIso
    (source (graph core1209) (root 9) 2 0) DegreeTwoThreeSpectrum1848.graph sourceMap1209swap=true := by decide +kernel
theorem fusedMap1209swap_checked : acceptsGraphIso
    (fused (graph core1209) (root 9) 2 0) DegreeTwoThreeSpectrum1850.graph fusedMap1209swap=true := by decide +kernel
theorem certified1209swap : Certified (graph core1209) (root 9) 2 0 :=
  of_native_maps core1209 DegreeTwoThreeSpectrum1848.graph DegreeTwoThreeSpectrum1850.graph
    sourceMap1209swap fusedMap1209swap sourceMap1209swap_checked fusedMap1209swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1209
#print axioms sourceMap1209swap_checked
#print axioms fusedMap1209swap_checked
#print axioms certified1209swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
