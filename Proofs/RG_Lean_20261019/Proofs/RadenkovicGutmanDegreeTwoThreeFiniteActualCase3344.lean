/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3344 : Family 9 := level9.get ⟨356,by decide⟩
def sourceMap3344 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3344 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3344_checked : acceptsGraphIso
    (source (graph core3344) (root 9) 0 5) DegreeTwoThreeSpectrum6188.graph sourceMap3344=true := by decide +kernel
theorem fusedMap3344_checked : acceptsGraphIso
    (fused (graph core3344) (root 9) 0 5) DegreeTwoThreeSpectrum5226.graph fusedMap3344=true := by decide +kernel
theorem certified3344 : Certified (graph core3344) (root 9) 0 5 :=
  of_native_maps core3344 DegreeTwoThreeSpectrum6188.graph DegreeTwoThreeSpectrum5226.graph
    sourceMap3344 fusedMap3344 sourceMap3344_checked fusedMap3344_checked
    DegreeTwoThreeFiniteComparisons.comparison3344
#print axioms sourceMap3344_checked
#print axioms fusedMap3344_checked
#print axioms certified3344
def sourceMap3344swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3344swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3344swap_checked : acceptsGraphIso
    (source (graph core3344) (root 9) 5 0) DegreeTwoThreeSpectrum6188.graph sourceMap3344swap=true := by decide +kernel
theorem fusedMap3344swap_checked : acceptsGraphIso
    (fused (graph core3344) (root 9) 5 0) DegreeTwoThreeSpectrum5226.graph fusedMap3344swap=true := by decide +kernel
theorem certified3344swap : Certified (graph core3344) (root 9) 5 0 :=
  of_native_maps core3344 DegreeTwoThreeSpectrum6188.graph DegreeTwoThreeSpectrum5226.graph
    sourceMap3344swap fusedMap3344swap sourceMap3344swap_checked fusedMap3344swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3344
#print axioms sourceMap3344swap_checked
#print axioms fusedMap3344swap_checked
#print axioms certified3344swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
