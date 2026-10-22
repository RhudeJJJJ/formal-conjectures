/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3371 : Family 9 := level9.get ⟨424,by decide⟩
def sourceMap3371 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3371 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3371_checked : acceptsGraphIso
    (source (graph core3371) (root 9) 0 5) DegreeTwoThreeSpectrum6522.graph sourceMap3371=true := by decide +kernel
theorem fusedMap3371_checked : acceptsGraphIso
    (fused (graph core3371) (root 9) 0 5) DegreeTwoThreeSpectrum5432.graph fusedMap3371=true := by decide +kernel
theorem certified3371 : Certified (graph core3371) (root 9) 0 5 :=
  of_native_maps core3371 DegreeTwoThreeSpectrum6522.graph DegreeTwoThreeSpectrum5432.graph
    sourceMap3371 fusedMap3371 sourceMap3371_checked fusedMap3371_checked
    DegreeTwoThreeFiniteComparisons.comparison3371
#print axioms sourceMap3371_checked
#print axioms fusedMap3371_checked
#print axioms certified3371
def sourceMap3371swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3371swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3371swap_checked : acceptsGraphIso
    (source (graph core3371) (root 9) 5 0) DegreeTwoThreeSpectrum6522.graph sourceMap3371swap=true := by decide +kernel
theorem fusedMap3371swap_checked : acceptsGraphIso
    (fused (graph core3371) (root 9) 5 0) DegreeTwoThreeSpectrum5432.graph fusedMap3371swap=true := by decide +kernel
theorem certified3371swap : Certified (graph core3371) (root 9) 5 0 :=
  of_native_maps core3371 DegreeTwoThreeSpectrum6522.graph DegreeTwoThreeSpectrum5432.graph
    sourceMap3371swap fusedMap3371swap sourceMap3371swap_checked fusedMap3371swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3371
#print axioms sourceMap3371swap_checked
#print axioms fusedMap3371swap_checked
#print axioms certified3371swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
