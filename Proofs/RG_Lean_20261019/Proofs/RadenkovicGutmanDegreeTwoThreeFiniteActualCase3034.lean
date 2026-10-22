/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3034 : Family 10 := level10.get ⟨1648,by decide⟩
def sourceMap3034 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3034 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3034_checked : acceptsGraphIso
    (source (graph core3034) (root 10) 0 4) DegreeTwoThreeSpectrum7208.graph sourceMap3034=true := by decide +kernel
theorem fusedMap3034_checked : acceptsGraphIso
    (fused (graph core3034) (root 10) 0 4) DegreeTwoThreeSpectrum6238.graph fusedMap3034=true := by decide +kernel
theorem certified3034 : Certified (graph core3034) (root 10) 0 4 :=
  of_native_maps core3034 DegreeTwoThreeSpectrum7208.graph DegreeTwoThreeSpectrum6238.graph
    sourceMap3034 fusedMap3034 sourceMap3034_checked fusedMap3034_checked
    DegreeTwoThreeFiniteComparisons.comparison3034
#print axioms sourceMap3034_checked
#print axioms fusedMap3034_checked
#print axioms certified3034
def sourceMap3034swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3034swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3034swap_checked : acceptsGraphIso
    (source (graph core3034) (root 10) 4 0) DegreeTwoThreeSpectrum7208.graph sourceMap3034swap=true := by decide +kernel
theorem fusedMap3034swap_checked : acceptsGraphIso
    (fused (graph core3034) (root 10) 4 0) DegreeTwoThreeSpectrum6238.graph fusedMap3034swap=true := by decide +kernel
theorem certified3034swap : Certified (graph core3034) (root 10) 4 0 :=
  of_native_maps core3034 DegreeTwoThreeSpectrum7208.graph DegreeTwoThreeSpectrum6238.graph
    sourceMap3034swap fusedMap3034swap sourceMap3034swap_checked fusedMap3034swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3034
#print axioms sourceMap3034swap_checked
#print axioms fusedMap3034swap_checked
#print axioms certified3034swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
