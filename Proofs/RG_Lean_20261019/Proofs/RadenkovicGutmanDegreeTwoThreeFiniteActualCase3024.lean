/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3024 : Family 10 := level10.get ⟨1627,by decide⟩
def sourceMap3024 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3024 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3024_checked : acceptsGraphIso
    (source (graph core3024) (root 10) 0 4) DegreeTwoThreeSpectrum7183.graph sourceMap3024=true := by decide +kernel
theorem fusedMap3024_checked : acceptsGraphIso
    (fused (graph core3024) (root 10) 0 4) DegreeTwoThreeSpectrum6190.graph fusedMap3024=true := by decide +kernel
theorem certified3024 : Certified (graph core3024) (root 10) 0 4 :=
  of_native_maps core3024 DegreeTwoThreeSpectrum7183.graph DegreeTwoThreeSpectrum6190.graph
    sourceMap3024 fusedMap3024 sourceMap3024_checked fusedMap3024_checked
    DegreeTwoThreeFiniteComparisons.comparison3024
#print axioms sourceMap3024_checked
#print axioms fusedMap3024_checked
#print axioms certified3024
def sourceMap3024swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3024swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3024swap_checked : acceptsGraphIso
    (source (graph core3024) (root 10) 4 0) DegreeTwoThreeSpectrum7183.graph sourceMap3024swap=true := by decide +kernel
theorem fusedMap3024swap_checked : acceptsGraphIso
    (fused (graph core3024) (root 10) 4 0) DegreeTwoThreeSpectrum6190.graph fusedMap3024swap=true := by decide +kernel
theorem certified3024swap : Certified (graph core3024) (root 10) 4 0 :=
  of_native_maps core3024 DegreeTwoThreeSpectrum7183.graph DegreeTwoThreeSpectrum6190.graph
    sourceMap3024swap fusedMap3024swap sourceMap3024swap_checked fusedMap3024swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3024
#print axioms sourceMap3024swap_checked
#print axioms fusedMap3024swap_checked
#print axioms certified3024swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
