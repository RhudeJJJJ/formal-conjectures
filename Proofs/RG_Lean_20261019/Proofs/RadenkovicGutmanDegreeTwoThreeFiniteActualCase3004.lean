/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3004 : Family 10 := level10.get ⟨1577,by decide⟩
def sourceMap3004 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3004 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3004_checked : acceptsGraphIso
    (source (graph core3004) (root 10) 0 4) DegreeTwoThreeSpectrum7115.graph sourceMap3004=true := by decide +kernel
theorem fusedMap3004_checked : acceptsGraphIso
    (fused (graph core3004) (root 10) 0 4) DegreeTwoThreeSpectrum6057.graph fusedMap3004=true := by decide +kernel
theorem certified3004 : Certified (graph core3004) (root 10) 0 4 :=
  of_native_maps core3004 DegreeTwoThreeSpectrum7115.graph DegreeTwoThreeSpectrum6057.graph
    sourceMap3004 fusedMap3004 sourceMap3004_checked fusedMap3004_checked
    DegreeTwoThreeFiniteComparisons.comparison3004
#print axioms sourceMap3004_checked
#print axioms fusedMap3004_checked
#print axioms certified3004
def sourceMap3004swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3004swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3004swap_checked : acceptsGraphIso
    (source (graph core3004) (root 10) 4 0) DegreeTwoThreeSpectrum7115.graph sourceMap3004swap=true := by decide +kernel
theorem fusedMap3004swap_checked : acceptsGraphIso
    (fused (graph core3004) (root 10) 4 0) DegreeTwoThreeSpectrum6057.graph fusedMap3004swap=true := by decide +kernel
theorem certified3004swap : Certified (graph core3004) (root 10) 4 0 :=
  of_native_maps core3004 DegreeTwoThreeSpectrum7115.graph DegreeTwoThreeSpectrum6057.graph
    sourceMap3004swap fusedMap3004swap sourceMap3004swap_checked fusedMap3004swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3004
#print axioms sourceMap3004swap_checked
#print axioms fusedMap3004swap_checked
#print axioms certified3004swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
