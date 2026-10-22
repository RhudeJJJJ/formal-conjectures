/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3205 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap3205 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3205 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3205_checked : acceptsGraphIso
    (source (graph core3205) (root 8) 0 5) DegreeTwoThreeSpectrum4212.graph sourceMap3205=true := by decide +kernel
theorem fusedMap3205_checked : acceptsGraphIso
    (fused (graph core3205) (root 8) 0 5) DegreeTwoThreeSpectrum4213.graph fusedMap3205=true := by decide +kernel
theorem certified3205 : Certified (graph core3205) (root 8) 0 5 :=
  of_native_maps core3205 DegreeTwoThreeSpectrum4212.graph DegreeTwoThreeSpectrum4213.graph
    sourceMap3205 fusedMap3205 sourceMap3205_checked fusedMap3205_checked
    DegreeTwoThreeFiniteComparisons.comparison3205
#print axioms sourceMap3205_checked
#print axioms fusedMap3205_checked
#print axioms certified3205
def sourceMap3205swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3205swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3205swap_checked : acceptsGraphIso
    (source (graph core3205) (root 8) 5 0) DegreeTwoThreeSpectrum4212.graph sourceMap3205swap=true := by decide +kernel
theorem fusedMap3205swap_checked : acceptsGraphIso
    (fused (graph core3205) (root 8) 5 0) DegreeTwoThreeSpectrum4213.graph fusedMap3205swap=true := by decide +kernel
theorem certified3205swap : Certified (graph core3205) (root 8) 5 0 :=
  of_native_maps core3205 DegreeTwoThreeSpectrum4212.graph DegreeTwoThreeSpectrum4213.graph
    sourceMap3205swap fusedMap3205swap sourceMap3205swap_checked fusedMap3205swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3205
#print axioms sourceMap3205swap_checked
#print axioms fusedMap3205swap_checked
#print axioms certified3205swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
