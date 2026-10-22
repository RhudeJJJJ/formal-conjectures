/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3007 : Family 10 := level10.get ⟨1584,by decide⟩
def sourceMap3007 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3007 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3007_checked : acceptsGraphIso
    (source (graph core3007) (root 10) 0 4) DegreeTwoThreeSpectrum7122.graph sourceMap3007=true := by decide +kernel
theorem fusedMap3007_checked : acceptsGraphIso
    (fused (graph core3007) (root 10) 0 4) DegreeTwoThreeSpectrum6073.graph fusedMap3007=true := by decide +kernel
theorem certified3007 : Certified (graph core3007) (root 10) 0 4 :=
  of_native_maps core3007 DegreeTwoThreeSpectrum7122.graph DegreeTwoThreeSpectrum6073.graph
    sourceMap3007 fusedMap3007 sourceMap3007_checked fusedMap3007_checked
    DegreeTwoThreeFiniteComparisons.comparison3007
#print axioms sourceMap3007_checked
#print axioms fusedMap3007_checked
#print axioms certified3007
def sourceMap3007swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3007swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3007swap_checked : acceptsGraphIso
    (source (graph core3007) (root 10) 4 0) DegreeTwoThreeSpectrum7122.graph sourceMap3007swap=true := by decide +kernel
theorem fusedMap3007swap_checked : acceptsGraphIso
    (fused (graph core3007) (root 10) 4 0) DegreeTwoThreeSpectrum6073.graph fusedMap3007swap=true := by decide +kernel
theorem certified3007swap : Certified (graph core3007) (root 10) 4 0 :=
  of_native_maps core3007 DegreeTwoThreeSpectrum7122.graph DegreeTwoThreeSpectrum6073.graph
    sourceMap3007swap fusedMap3007swap sourceMap3007swap_checked fusedMap3007swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3007
#print axioms sourceMap3007swap_checked
#print axioms fusedMap3007swap_checked
#print axioms certified3007swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
