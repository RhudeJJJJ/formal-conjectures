/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3900 : Family 8 := level8.get ⟨215,by decide⟩
def sourceMap3900 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3900 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3900_checked : acceptsGraphIso
    (source (graph core3900) (root 8) 1 4) DegreeTwoThreeSpectrum4736.graph sourceMap3900=true := by decide +kernel
theorem fusedMap3900_checked : acceptsGraphIso
    (fused (graph core3900) (root 8) 1 4) DegreeTwoThreeSpectrum4289.graph fusedMap3900=true := by decide +kernel
theorem certified3900 : Certified (graph core3900) (root 8) 1 4 :=
  of_native_maps core3900 DegreeTwoThreeSpectrum4736.graph DegreeTwoThreeSpectrum4289.graph
    sourceMap3900 fusedMap3900 sourceMap3900_checked fusedMap3900_checked
    DegreeTwoThreeFiniteComparisons.comparison3900
#print axioms sourceMap3900_checked
#print axioms fusedMap3900_checked
#print axioms certified3900
def sourceMap3900swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3900swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3900swap_checked : acceptsGraphIso
    (source (graph core3900) (root 8) 4 1) DegreeTwoThreeSpectrum4736.graph sourceMap3900swap=true := by decide +kernel
theorem fusedMap3900swap_checked : acceptsGraphIso
    (fused (graph core3900) (root 8) 4 1) DegreeTwoThreeSpectrum4289.graph fusedMap3900swap=true := by decide +kernel
theorem certified3900swap : Certified (graph core3900) (root 8) 4 1 :=
  of_native_maps core3900 DegreeTwoThreeSpectrum4736.graph DegreeTwoThreeSpectrum4289.graph
    sourceMap3900swap fusedMap3900swap sourceMap3900swap_checked fusedMap3900swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3900
#print axioms sourceMap3900swap_checked
#print axioms fusedMap3900swap_checked
#print axioms certified3900swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
