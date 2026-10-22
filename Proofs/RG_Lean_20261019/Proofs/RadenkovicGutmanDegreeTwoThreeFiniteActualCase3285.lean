/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3285 : Family 9 := level9.get ⟨192,by decide⟩
def sourceMap3285 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3285 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3285_checked : acceptsGraphIso
    (source (graph core3285) (root 9) 0 5) DegreeTwoThreeSpectrum5381.graph sourceMap3285=true := by decide +kernel
theorem fusedMap3285_checked : acceptsGraphIso
    (fused (graph core3285) (root 9) 0 5) DegreeTwoThreeSpectrum5382.graph fusedMap3285=true := by decide +kernel
theorem certified3285 : Certified (graph core3285) (root 9) 0 5 :=
  of_native_maps core3285 DegreeTwoThreeSpectrum5381.graph DegreeTwoThreeSpectrum5382.graph
    sourceMap3285 fusedMap3285 sourceMap3285_checked fusedMap3285_checked
    DegreeTwoThreeFiniteComparisons.comparison3285
#print axioms sourceMap3285_checked
#print axioms fusedMap3285_checked
#print axioms certified3285
def sourceMap3285swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3285swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3285swap_checked : acceptsGraphIso
    (source (graph core3285) (root 9) 5 0) DegreeTwoThreeSpectrum5381.graph sourceMap3285swap=true := by decide +kernel
theorem fusedMap3285swap_checked : acceptsGraphIso
    (fused (graph core3285) (root 9) 5 0) DegreeTwoThreeSpectrum5382.graph fusedMap3285swap=true := by decide +kernel
theorem certified3285swap : Certified (graph core3285) (root 9) 5 0 :=
  of_native_maps core3285 DegreeTwoThreeSpectrum5381.graph DegreeTwoThreeSpectrum5382.graph
    sourceMap3285swap fusedMap3285swap sourceMap3285swap_checked fusedMap3285swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3285
#print axioms sourceMap3285swap_checked
#print axioms fusedMap3285swap_checked
#print axioms certified3285swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
