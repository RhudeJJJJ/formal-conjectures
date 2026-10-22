/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3246 : Family 9 := level9.get ⟨59,by decide⟩
def sourceMap3246 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3246 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3246_checked : acceptsGraphIso
    (source (graph core3246) (root 9) 0 5) DegreeTwoThreeSpectrum5361.graph sourceMap3246=true := by decide +kernel
theorem fusedMap3246_checked : acceptsGraphIso
    (fused (graph core3246) (root 9) 0 5) DegreeTwoThreeSpectrum4985.graph fusedMap3246=true := by decide +kernel
theorem certified3246 : Certified (graph core3246) (root 9) 0 5 :=
  of_native_maps core3246 DegreeTwoThreeSpectrum5361.graph DegreeTwoThreeSpectrum4985.graph
    sourceMap3246 fusedMap3246 sourceMap3246_checked fusedMap3246_checked
    DegreeTwoThreeFiniteComparisons.comparison3246
#print axioms sourceMap3246_checked
#print axioms fusedMap3246_checked
#print axioms certified3246
def sourceMap3246swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3246swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3246swap_checked : acceptsGraphIso
    (source (graph core3246) (root 9) 5 0) DegreeTwoThreeSpectrum5361.graph sourceMap3246swap=true := by decide +kernel
theorem fusedMap3246swap_checked : acceptsGraphIso
    (fused (graph core3246) (root 9) 5 0) DegreeTwoThreeSpectrum4985.graph fusedMap3246swap=true := by decide +kernel
theorem certified3246swap : Certified (graph core3246) (root 9) 5 0 :=
  of_native_maps core3246 DegreeTwoThreeSpectrum5361.graph DegreeTwoThreeSpectrum4985.graph
    sourceMap3246swap fusedMap3246swap sourceMap3246swap_checked fusedMap3246swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3246
#print axioms sourceMap3246swap_checked
#print axioms fusedMap3246swap_checked
#print axioms certified3246swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
