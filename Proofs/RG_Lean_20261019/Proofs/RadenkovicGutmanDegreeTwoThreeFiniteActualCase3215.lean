/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3215 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap3215 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3215 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3215_checked : acceptsGraphIso
    (source (graph core3215) (root 8) 0 5) DegreeTwoThreeSpectrum4305.graph sourceMap3215=true := by decide +kernel
theorem fusedMap3215_checked : acceptsGraphIso
    (fused (graph core3215) (root 8) 0 5) DegreeTwoThreeSpectrum4306.graph fusedMap3215=true := by decide +kernel
theorem certified3215 : Certified (graph core3215) (root 8) 0 5 :=
  of_native_maps core3215 DegreeTwoThreeSpectrum4305.graph DegreeTwoThreeSpectrum4306.graph
    sourceMap3215 fusedMap3215 sourceMap3215_checked fusedMap3215_checked
    DegreeTwoThreeFiniteComparisons.comparison3215
#print axioms sourceMap3215_checked
#print axioms fusedMap3215_checked
#print axioms certified3215
def sourceMap3215swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3215swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3215swap_checked : acceptsGraphIso
    (source (graph core3215) (root 8) 5 0) DegreeTwoThreeSpectrum4305.graph sourceMap3215swap=true := by decide +kernel
theorem fusedMap3215swap_checked : acceptsGraphIso
    (fused (graph core3215) (root 8) 5 0) DegreeTwoThreeSpectrum4306.graph fusedMap3215swap=true := by decide +kernel
theorem certified3215swap : Certified (graph core3215) (root 8) 5 0 :=
  of_native_maps core3215 DegreeTwoThreeSpectrum4305.graph DegreeTwoThreeSpectrum4306.graph
    sourceMap3215swap fusedMap3215swap sourceMap3215swap_checked fusedMap3215swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3215
#print axioms sourceMap3215swap_checked
#print axioms fusedMap3215swap_checked
#print axioms certified3215swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
