/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3237 : Family 9 := level9.get ⟨15,by decide⟩
def sourceMap3237 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3237 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 0 5 v)
theorem sourceMap3237_checked : acceptsGraphIso
    (source (graph core3237) (root 9) 0 5) DegreeTwoThreeSpectrum5005.graph sourceMap3237=true := by decide +kernel
theorem fusedMap3237_checked : acceptsGraphIso
    (fused (graph core3237) (root 9) 0 5) DegreeTwoThreeSpectrum5007.graph fusedMap3237=true := by decide +kernel
theorem certified3237 : Certified (graph core3237) (root 9) 0 5 :=
  of_native_maps core3237 DegreeTwoThreeSpectrum5005.graph DegreeTwoThreeSpectrum5007.graph
    sourceMap3237 fusedMap3237 sourceMap3237_checked fusedMap3237_checked
    DegreeTwoThreeFiniteComparisons.comparison3237
#print axioms sourceMap3237_checked
#print axioms fusedMap3237_checked
#print axioms certified3237
def sourceMap3237swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3237swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,16,9,10,11,12,13,14,15] (fusedLabel 9 5 0 v)
theorem sourceMap3237swap_checked : acceptsGraphIso
    (source (graph core3237) (root 9) 5 0) DegreeTwoThreeSpectrum5005.graph sourceMap3237swap=true := by decide +kernel
theorem fusedMap3237swap_checked : acceptsGraphIso
    (fused (graph core3237) (root 9) 5 0) DegreeTwoThreeSpectrum5007.graph fusedMap3237swap=true := by decide +kernel
theorem certified3237swap : Certified (graph core3237) (root 9) 5 0 :=
  of_native_maps core3237 DegreeTwoThreeSpectrum5005.graph DegreeTwoThreeSpectrum5007.graph
    sourceMap3237swap fusedMap3237swap sourceMap3237swap_checked fusedMap3237swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3237
#print axioms sourceMap3237swap_checked
#print axioms fusedMap3237swap_checked
#print axioms certified3237swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
