/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3014 : Family 10 := level10.get ⟨1599,by decide⟩
def sourceMap3014 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3014 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3014_checked : acceptsGraphIso
    (source (graph core3014) (root 10) 0 4) DegreeTwoThreeSpectrum7143.graph sourceMap3014=true := by decide +kernel
theorem fusedMap3014_checked : acceptsGraphIso
    (fused (graph core3014) (root 10) 0 4) DegreeTwoThreeSpectrum6114.graph fusedMap3014=true := by decide +kernel
theorem certified3014 : Certified (graph core3014) (root 10) 0 4 :=
  of_native_maps core3014 DegreeTwoThreeSpectrum7143.graph DegreeTwoThreeSpectrum6114.graph
    sourceMap3014 fusedMap3014 sourceMap3014_checked fusedMap3014_checked
    DegreeTwoThreeFiniteComparisons.comparison3014
#print axioms sourceMap3014_checked
#print axioms fusedMap3014_checked
#print axioms certified3014
def sourceMap3014swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3014swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3014swap_checked : acceptsGraphIso
    (source (graph core3014) (root 10) 4 0) DegreeTwoThreeSpectrum7143.graph sourceMap3014swap=true := by decide +kernel
theorem fusedMap3014swap_checked : acceptsGraphIso
    (fused (graph core3014) (root 10) 4 0) DegreeTwoThreeSpectrum6114.graph fusedMap3014swap=true := by decide +kernel
theorem certified3014swap : Certified (graph core3014) (root 10) 4 0 :=
  of_native_maps core3014 DegreeTwoThreeSpectrum7143.graph DegreeTwoThreeSpectrum6114.graph
    sourceMap3014swap fusedMap3014swap sourceMap3014swap_checked fusedMap3014swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3014
#print axioms sourceMap3014swap_checked
#print axioms fusedMap3014swap_checked
#print axioms certified3014swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
