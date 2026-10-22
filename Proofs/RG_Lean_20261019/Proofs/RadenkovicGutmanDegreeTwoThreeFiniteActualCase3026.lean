/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3026 : Family 10 := level10.get ⟨1631,by decide⟩
def sourceMap3026 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3026 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3026_checked : acceptsGraphIso
    (source (graph core3026) (root 10) 0 4) DegreeTwoThreeSpectrum7186.graph sourceMap3026=true := by decide +kernel
theorem fusedMap3026_checked : acceptsGraphIso
    (fused (graph core3026) (root 10) 0 4) DegreeTwoThreeSpectrum6196.graph fusedMap3026=true := by decide +kernel
theorem certified3026 : Certified (graph core3026) (root 10) 0 4 :=
  of_native_maps core3026 DegreeTwoThreeSpectrum7186.graph DegreeTwoThreeSpectrum6196.graph
    sourceMap3026 fusedMap3026 sourceMap3026_checked fusedMap3026_checked
    DegreeTwoThreeFiniteComparisons.comparison3026
#print axioms sourceMap3026_checked
#print axioms fusedMap3026_checked
#print axioms certified3026
def sourceMap3026swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3026swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3026swap_checked : acceptsGraphIso
    (source (graph core3026) (root 10) 4 0) DegreeTwoThreeSpectrum7186.graph sourceMap3026swap=true := by decide +kernel
theorem fusedMap3026swap_checked : acceptsGraphIso
    (fused (graph core3026) (root 10) 4 0) DegreeTwoThreeSpectrum6196.graph fusedMap3026swap=true := by decide +kernel
theorem certified3026swap : Certified (graph core3026) (root 10) 4 0 :=
  of_native_maps core3026 DegreeTwoThreeSpectrum7186.graph DegreeTwoThreeSpectrum6196.graph
    sourceMap3026swap fusedMap3026swap sourceMap3026swap_checked fusedMap3026swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3026
#print axioms sourceMap3026swap_checked
#print axioms fusedMap3026swap_checked
#print axioms certified3026swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
