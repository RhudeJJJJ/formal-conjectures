/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3382 : Family 9 := level9.get ⟨452,by decide⟩
def sourceMap3382 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3382 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3382_checked : acceptsGraphIso
    (source (graph core3382) (root 9) 0 5) DegreeTwoThreeSpectrum6649.graph sourceMap3382=true := by decide +kernel
theorem fusedMap3382_checked : acceptsGraphIso
    (fused (graph core3382) (root 9) 0 5) DegreeTwoThreeSpectrum5508.graph fusedMap3382=true := by decide +kernel
theorem certified3382 : Certified (graph core3382) (root 9) 0 5 :=
  of_native_maps core3382 DegreeTwoThreeSpectrum6649.graph DegreeTwoThreeSpectrum5508.graph
    sourceMap3382 fusedMap3382 sourceMap3382_checked fusedMap3382_checked
    DegreeTwoThreeFiniteComparisons.comparison3382
#print axioms sourceMap3382_checked
#print axioms fusedMap3382_checked
#print axioms certified3382
def sourceMap3382swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3382swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3382swap_checked : acceptsGraphIso
    (source (graph core3382) (root 9) 5 0) DegreeTwoThreeSpectrum6649.graph sourceMap3382swap=true := by decide +kernel
theorem fusedMap3382swap_checked : acceptsGraphIso
    (fused (graph core3382) (root 9) 5 0) DegreeTwoThreeSpectrum5508.graph fusedMap3382swap=true := by decide +kernel
theorem certified3382swap : Certified (graph core3382) (root 9) 5 0 :=
  of_native_maps core3382 DegreeTwoThreeSpectrum6649.graph DegreeTwoThreeSpectrum5508.graph
    sourceMap3382swap fusedMap3382swap sourceMap3382swap_checked fusedMap3382swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3382
#print axioms sourceMap3382swap_checked
#print axioms fusedMap3382swap_checked
#print axioms certified3382swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
