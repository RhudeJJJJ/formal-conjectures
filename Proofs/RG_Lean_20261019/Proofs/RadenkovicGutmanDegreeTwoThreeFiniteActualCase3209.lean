/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3209 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap3209 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3209 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3209_checked : acceptsGraphIso
    (source (graph core3209) (root 8) 0 5) DegreeTwoThreeSpectrum4238.graph sourceMap3209=true := by decide +kernel
theorem fusedMap3209_checked : acceptsGraphIso
    (fused (graph core3209) (root 8) 0 5) DegreeTwoThreeSpectrum4239.graph fusedMap3209=true := by decide +kernel
theorem certified3209 : Certified (graph core3209) (root 8) 0 5 :=
  of_native_maps core3209 DegreeTwoThreeSpectrum4238.graph DegreeTwoThreeSpectrum4239.graph
    sourceMap3209 fusedMap3209 sourceMap3209_checked fusedMap3209_checked
    DegreeTwoThreeFiniteComparisons.comparison3209
#print axioms sourceMap3209_checked
#print axioms fusedMap3209_checked
#print axioms certified3209
def sourceMap3209swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3209swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3209swap_checked : acceptsGraphIso
    (source (graph core3209) (root 8) 5 0) DegreeTwoThreeSpectrum4238.graph sourceMap3209swap=true := by decide +kernel
theorem fusedMap3209swap_checked : acceptsGraphIso
    (fused (graph core3209) (root 8) 5 0) DegreeTwoThreeSpectrum4239.graph fusedMap3209swap=true := by decide +kernel
theorem certified3209swap : Certified (graph core3209) (root 8) 5 0 :=
  of_native_maps core3209 DegreeTwoThreeSpectrum4238.graph DegreeTwoThreeSpectrum4239.graph
    sourceMap3209swap fusedMap3209swap sourceMap3209swap_checked fusedMap3209swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3209
#print axioms sourceMap3209swap_checked
#print axioms fusedMap3209swap_checked
#print axioms certified3209swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
