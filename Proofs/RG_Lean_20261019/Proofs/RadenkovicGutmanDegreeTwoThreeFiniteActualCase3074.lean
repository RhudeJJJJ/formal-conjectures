/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3074 : Family 10 := level10.get ⟨1807,by decide⟩
def sourceMap3074 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3074 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3074_checked : acceptsGraphIso
    (source (graph core3074) (root 10) 0 4) DegreeTwoThreeSpectrum7069.graph sourceMap3074=true := by decide +kernel
theorem fusedMap3074_checked : acceptsGraphIso
    (fused (graph core3074) (root 10) 0 4) DegreeTwoThreeSpectrum7070.graph fusedMap3074=true := by decide +kernel
theorem certified3074 : Certified (graph core3074) (root 10) 0 4 :=
  of_native_maps core3074 DegreeTwoThreeSpectrum7069.graph DegreeTwoThreeSpectrum7070.graph
    sourceMap3074 fusedMap3074 sourceMap3074_checked fusedMap3074_checked
    DegreeTwoThreeFiniteComparisons.comparison3074
#print axioms sourceMap3074_checked
#print axioms fusedMap3074_checked
#print axioms certified3074
def sourceMap3074swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3074swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3074swap_checked : acceptsGraphIso
    (source (graph core3074) (root 10) 4 0) DegreeTwoThreeSpectrum7069.graph sourceMap3074swap=true := by decide +kernel
theorem fusedMap3074swap_checked : acceptsGraphIso
    (fused (graph core3074) (root 10) 4 0) DegreeTwoThreeSpectrum7070.graph fusedMap3074swap=true := by decide +kernel
theorem certified3074swap : Certified (graph core3074) (root 10) 4 0 :=
  of_native_maps core3074 DegreeTwoThreeSpectrum7069.graph DegreeTwoThreeSpectrum7070.graph
    sourceMap3074swap fusedMap3074swap sourceMap3074swap_checked fusedMap3074swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3074
#print axioms sourceMap3074swap_checked
#print axioms fusedMap3074swap_checked
#print axioms certified3074swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
