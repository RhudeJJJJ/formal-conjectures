/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3001 : Family 10 := level10.get ⟨1571,by decide⟩
def sourceMap3001 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3001 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3001_checked : acceptsGraphIso
    (source (graph core3001) (root 10) 0 4) DegreeTwoThreeSpectrum7111.graph sourceMap3001=true := by decide +kernel
theorem fusedMap3001_checked : acceptsGraphIso
    (fused (graph core3001) (root 10) 0 4) DegreeTwoThreeSpectrum6050.graph fusedMap3001=true := by decide +kernel
theorem certified3001 : Certified (graph core3001) (root 10) 0 4 :=
  of_native_maps core3001 DegreeTwoThreeSpectrum7111.graph DegreeTwoThreeSpectrum6050.graph
    sourceMap3001 fusedMap3001 sourceMap3001_checked fusedMap3001_checked
    DegreeTwoThreeFiniteComparisons.comparison3001
#print axioms sourceMap3001_checked
#print axioms fusedMap3001_checked
#print axioms certified3001
def sourceMap3001swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3001swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3001swap_checked : acceptsGraphIso
    (source (graph core3001) (root 10) 4 0) DegreeTwoThreeSpectrum7111.graph sourceMap3001swap=true := by decide +kernel
theorem fusedMap3001swap_checked : acceptsGraphIso
    (fused (graph core3001) (root 10) 4 0) DegreeTwoThreeSpectrum6050.graph fusedMap3001swap=true := by decide +kernel
theorem certified3001swap : Certified (graph core3001) (root 10) 4 0 :=
  of_native_maps core3001 DegreeTwoThreeSpectrum7111.graph DegreeTwoThreeSpectrum6050.graph
    sourceMap3001swap fusedMap3001swap sourceMap3001swap_checked fusedMap3001swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3001
#print axioms sourceMap3001swap_checked
#print axioms fusedMap3001swap_checked
#print axioms certified3001swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
