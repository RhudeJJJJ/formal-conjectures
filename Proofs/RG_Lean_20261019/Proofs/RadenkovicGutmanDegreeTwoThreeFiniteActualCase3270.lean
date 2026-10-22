/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3270 : Family 9 := level9.get ⟨141,by decide⟩
def sourceMap3270 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3270 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3270_checked : acceptsGraphIso
    (source (graph core3270) (root 9) 0 5) DegreeTwoThreeSpectrum5155.graph sourceMap3270=true := by decide +kernel
theorem fusedMap3270_checked : acceptsGraphIso
    (fused (graph core3270) (root 9) 0 5) DegreeTwoThreeSpectrum5156.graph fusedMap3270=true := by decide +kernel
theorem certified3270 : Certified (graph core3270) (root 9) 0 5 :=
  of_native_maps core3270 DegreeTwoThreeSpectrum5155.graph DegreeTwoThreeSpectrum5156.graph
    sourceMap3270 fusedMap3270 sourceMap3270_checked fusedMap3270_checked
    DegreeTwoThreeFiniteComparisons.comparison3270
#print axioms sourceMap3270_checked
#print axioms fusedMap3270_checked
#print axioms certified3270
def sourceMap3270swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3270swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3270swap_checked : acceptsGraphIso
    (source (graph core3270) (root 9) 5 0) DegreeTwoThreeSpectrum5155.graph sourceMap3270swap=true := by decide +kernel
theorem fusedMap3270swap_checked : acceptsGraphIso
    (fused (graph core3270) (root 9) 5 0) DegreeTwoThreeSpectrum5156.graph fusedMap3270swap=true := by decide +kernel
theorem certified3270swap : Certified (graph core3270) (root 9) 5 0 :=
  of_native_maps core3270 DegreeTwoThreeSpectrum5155.graph DegreeTwoThreeSpectrum5156.graph
    sourceMap3270swap fusedMap3270swap sourceMap3270swap_checked fusedMap3270swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3270
#print axioms sourceMap3270swap_checked
#print axioms fusedMap3270swap_checked
#print axioms certified3270swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
