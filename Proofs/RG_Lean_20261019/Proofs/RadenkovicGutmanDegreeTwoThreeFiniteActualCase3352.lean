/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3352 : Family 9 := level9.get ⟨379,by decide⟩
def sourceMap3352 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3352 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3352_checked : acceptsGraphIso
    (source (graph core3352) (root 9) 0 5) DegreeTwoThreeSpectrum6305.graph sourceMap3352=true := by decide +kernel
theorem fusedMap3352_checked : acceptsGraphIso
    (fused (graph core3352) (root 9) 0 5) DegreeTwoThreeSpectrum5270.graph fusedMap3352=true := by decide +kernel
theorem certified3352 : Certified (graph core3352) (root 9) 0 5 :=
  of_native_maps core3352 DegreeTwoThreeSpectrum6305.graph DegreeTwoThreeSpectrum5270.graph
    sourceMap3352 fusedMap3352 sourceMap3352_checked fusedMap3352_checked
    DegreeTwoThreeFiniteComparisons.comparison3352
#print axioms sourceMap3352_checked
#print axioms fusedMap3352_checked
#print axioms certified3352
def sourceMap3352swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3352swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3352swap_checked : acceptsGraphIso
    (source (graph core3352) (root 9) 5 0) DegreeTwoThreeSpectrum6305.graph sourceMap3352swap=true := by decide +kernel
theorem fusedMap3352swap_checked : acceptsGraphIso
    (fused (graph core3352) (root 9) 5 0) DegreeTwoThreeSpectrum5270.graph fusedMap3352swap=true := by decide +kernel
theorem certified3352swap : Certified (graph core3352) (root 9) 5 0 :=
  of_native_maps core3352 DegreeTwoThreeSpectrum6305.graph DegreeTwoThreeSpectrum5270.graph
    sourceMap3352swap fusedMap3352swap sourceMap3352swap_checked fusedMap3352swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3352
#print axioms sourceMap3352swap_checked
#print axioms fusedMap3352swap_checked
#print axioms certified3352swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
