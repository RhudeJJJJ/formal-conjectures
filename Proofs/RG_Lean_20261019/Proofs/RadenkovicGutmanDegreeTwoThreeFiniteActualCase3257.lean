/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3257 : Family 9 := level9.get ⟨102,by decide⟩
def sourceMap3257 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3257 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3257_checked : acceptsGraphIso
    (source (graph core3257) (root 9) 0 5) DegreeTwoThreeSpectrum5759.graph sourceMap3257=true := by decide +kernel
theorem fusedMap3257_checked : acceptsGraphIso
    (fused (graph core3257) (root 9) 0 5) DegreeTwoThreeSpectrum5058.graph fusedMap3257=true := by decide +kernel
theorem certified3257 : Certified (graph core3257) (root 9) 0 5 :=
  of_native_maps core3257 DegreeTwoThreeSpectrum5759.graph DegreeTwoThreeSpectrum5058.graph
    sourceMap3257 fusedMap3257 sourceMap3257_checked fusedMap3257_checked
    DegreeTwoThreeFiniteComparisons.comparison3257
#print axioms sourceMap3257_checked
#print axioms fusedMap3257_checked
#print axioms certified3257
def sourceMap3257swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3257swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3257swap_checked : acceptsGraphIso
    (source (graph core3257) (root 9) 5 0) DegreeTwoThreeSpectrum5759.graph sourceMap3257swap=true := by decide +kernel
theorem fusedMap3257swap_checked : acceptsGraphIso
    (fused (graph core3257) (root 9) 5 0) DegreeTwoThreeSpectrum5058.graph fusedMap3257swap=true := by decide +kernel
theorem certified3257swap : Certified (graph core3257) (root 9) 5 0 :=
  of_native_maps core3257 DegreeTwoThreeSpectrum5759.graph DegreeTwoThreeSpectrum5058.graph
    sourceMap3257swap fusedMap3257swap sourceMap3257swap_checked fusedMap3257swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3257
#print axioms sourceMap3257swap_checked
#print axioms fusedMap3257swap_checked
#print axioms certified3257swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
