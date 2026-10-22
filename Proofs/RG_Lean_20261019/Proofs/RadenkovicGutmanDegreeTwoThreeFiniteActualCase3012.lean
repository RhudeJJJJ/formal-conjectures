/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3012 : Family 10 := level10.get ⟨1592,by decide⟩
def sourceMap3012 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3012 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3012_checked : acceptsGraphIso
    (source (graph core3012) (root 10) 0 4) DegreeTwoThreeSpectrum7131.graph sourceMap3012=true := by decide +kernel
theorem fusedMap3012_checked : acceptsGraphIso
    (fused (graph core3012) (root 10) 0 4) DegreeTwoThreeSpectrum6091.graph fusedMap3012=true := by decide +kernel
theorem certified3012 : Certified (graph core3012) (root 10) 0 4 :=
  of_native_maps core3012 DegreeTwoThreeSpectrum7131.graph DegreeTwoThreeSpectrum6091.graph
    sourceMap3012 fusedMap3012 sourceMap3012_checked fusedMap3012_checked
    DegreeTwoThreeFiniteComparisons.comparison3012
#print axioms sourceMap3012_checked
#print axioms fusedMap3012_checked
#print axioms certified3012
def sourceMap3012swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3012swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3012swap_checked : acceptsGraphIso
    (source (graph core3012) (root 10) 4 0) DegreeTwoThreeSpectrum7131.graph sourceMap3012swap=true := by decide +kernel
theorem fusedMap3012swap_checked : acceptsGraphIso
    (fused (graph core3012) (root 10) 4 0) DegreeTwoThreeSpectrum6091.graph fusedMap3012swap=true := by decide +kernel
theorem certified3012swap : Certified (graph core3012) (root 10) 4 0 :=
  of_native_maps core3012 DegreeTwoThreeSpectrum7131.graph DegreeTwoThreeSpectrum6091.graph
    sourceMap3012swap fusedMap3012swap sourceMap3012swap_checked fusedMap3012swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3012
#print axioms sourceMap3012swap_checked
#print axioms fusedMap3012swap_checked
#print axioms certified3012swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
