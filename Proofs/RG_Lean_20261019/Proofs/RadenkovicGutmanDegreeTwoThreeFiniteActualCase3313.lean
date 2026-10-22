/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3313 : Family 9 := level9.get ⟨273,by decide⟩
def sourceMap3313 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3313 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3313_checked : acceptsGraphIso
    (source (graph core3313) (root 9) 0 5) DegreeTwoThreeSpectrum5751.graph sourceMap3313=true := by decide +kernel
theorem fusedMap3313_checked : acceptsGraphIso
    (fused (graph core3313) (root 9) 0 5) DegreeTwoThreeSpectrum5752.graph fusedMap3313=true := by decide +kernel
theorem certified3313 : Certified (graph core3313) (root 9) 0 5 :=
  of_native_maps core3313 DegreeTwoThreeSpectrum5751.graph DegreeTwoThreeSpectrum5752.graph
    sourceMap3313 fusedMap3313 sourceMap3313_checked fusedMap3313_checked
    DegreeTwoThreeFiniteComparisons.comparison3313
#print axioms sourceMap3313_checked
#print axioms fusedMap3313_checked
#print axioms certified3313
def sourceMap3313swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3313swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3313swap_checked : acceptsGraphIso
    (source (graph core3313) (root 9) 5 0) DegreeTwoThreeSpectrum5751.graph sourceMap3313swap=true := by decide +kernel
theorem fusedMap3313swap_checked : acceptsGraphIso
    (fused (graph core3313) (root 9) 5 0) DegreeTwoThreeSpectrum5752.graph fusedMap3313swap=true := by decide +kernel
theorem certified3313swap : Certified (graph core3313) (root 9) 5 0 :=
  of_native_maps core3313 DegreeTwoThreeSpectrum5751.graph DegreeTwoThreeSpectrum5752.graph
    sourceMap3313swap fusedMap3313swap sourceMap3313swap_checked fusedMap3313swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3313
#print axioms sourceMap3313swap_checked
#print axioms fusedMap3313swap_checked
#print axioms certified3313swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
