/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3208 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap3208 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3208 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3208_checked : acceptsGraphIso
    (source (graph core3208) (root 8) 0 5) DegreeTwoThreeSpectrum4235.graph sourceMap3208=true := by decide +kernel
theorem fusedMap3208_checked : acceptsGraphIso
    (fused (graph core3208) (root 8) 0 5) DegreeTwoThreeSpectrum4236.graph fusedMap3208=true := by decide +kernel
theorem certified3208 : Certified (graph core3208) (root 8) 0 5 :=
  of_native_maps core3208 DegreeTwoThreeSpectrum4235.graph DegreeTwoThreeSpectrum4236.graph
    sourceMap3208 fusedMap3208 sourceMap3208_checked fusedMap3208_checked
    DegreeTwoThreeFiniteComparisons.comparison3208
#print axioms sourceMap3208_checked
#print axioms fusedMap3208_checked
#print axioms certified3208
def sourceMap3208swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3208swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3208swap_checked : acceptsGraphIso
    (source (graph core3208) (root 8) 5 0) DegreeTwoThreeSpectrum4235.graph sourceMap3208swap=true := by decide +kernel
theorem fusedMap3208swap_checked : acceptsGraphIso
    (fused (graph core3208) (root 8) 5 0) DegreeTwoThreeSpectrum4236.graph fusedMap3208swap=true := by decide +kernel
theorem certified3208swap : Certified (graph core3208) (root 8) 5 0 :=
  of_native_maps core3208 DegreeTwoThreeSpectrum4235.graph DegreeTwoThreeSpectrum4236.graph
    sourceMap3208swap fusedMap3208swap sourceMap3208swap_checked fusedMap3208swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3208
#print axioms sourceMap3208swap_checked
#print axioms fusedMap3208swap_checked
#print axioms certified3208swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
