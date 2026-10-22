/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3013 : Family 10 := level10.get ⟨1594,by decide⟩
def sourceMap3013 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3013 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3013_checked : acceptsGraphIso
    (source (graph core3013) (root 10) 0 4) DegreeTwoThreeSpectrum7134.graph sourceMap3013=true := by decide +kernel
theorem fusedMap3013_checked : acceptsGraphIso
    (fused (graph core3013) (root 10) 0 4) DegreeTwoThreeSpectrum6094.graph fusedMap3013=true := by decide +kernel
theorem certified3013 : Certified (graph core3013) (root 10) 0 4 :=
  of_native_maps core3013 DegreeTwoThreeSpectrum7134.graph DegreeTwoThreeSpectrum6094.graph
    sourceMap3013 fusedMap3013 sourceMap3013_checked fusedMap3013_checked
    DegreeTwoThreeFiniteComparisons.comparison3013
#print axioms sourceMap3013_checked
#print axioms fusedMap3013_checked
#print axioms certified3013
def sourceMap3013swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3013swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3013swap_checked : acceptsGraphIso
    (source (graph core3013) (root 10) 4 0) DegreeTwoThreeSpectrum7134.graph sourceMap3013swap=true := by decide +kernel
theorem fusedMap3013swap_checked : acceptsGraphIso
    (fused (graph core3013) (root 10) 4 0) DegreeTwoThreeSpectrum6094.graph fusedMap3013swap=true := by decide +kernel
theorem certified3013swap : Certified (graph core3013) (root 10) 4 0 :=
  of_native_maps core3013 DegreeTwoThreeSpectrum7134.graph DegreeTwoThreeSpectrum6094.graph
    sourceMap3013swap fusedMap3013swap sourceMap3013swap_checked fusedMap3013swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3013
#print axioms sourceMap3013swap_checked
#print axioms fusedMap3013swap_checked
#print axioms certified3013swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
