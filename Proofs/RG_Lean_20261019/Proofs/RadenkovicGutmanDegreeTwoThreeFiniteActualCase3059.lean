/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3059 : Family 10 := level10.get ⟨1725,by decide⟩
def sourceMap3059 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3059 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3059_checked : acceptsGraphIso
    (source (graph core3059) (root 10) 0 4) DegreeTwoThreeSpectrum7352.graph sourceMap3059=true := by decide +kernel
theorem fusedMap3059_checked : acceptsGraphIso
    (fused (graph core3059) (root 10) 0 4) DegreeTwoThreeSpectrum6527.graph fusedMap3059=true := by decide +kernel
theorem certified3059 : Certified (graph core3059) (root 10) 0 4 :=
  of_native_maps core3059 DegreeTwoThreeSpectrum7352.graph DegreeTwoThreeSpectrum6527.graph
    sourceMap3059 fusedMap3059 sourceMap3059_checked fusedMap3059_checked
    DegreeTwoThreeFiniteComparisons.comparison3059
#print axioms sourceMap3059_checked
#print axioms fusedMap3059_checked
#print axioms certified3059
def sourceMap3059swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3059swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3059swap_checked : acceptsGraphIso
    (source (graph core3059) (root 10) 4 0) DegreeTwoThreeSpectrum7352.graph sourceMap3059swap=true := by decide +kernel
theorem fusedMap3059swap_checked : acceptsGraphIso
    (fused (graph core3059) (root 10) 4 0) DegreeTwoThreeSpectrum6527.graph fusedMap3059swap=true := by decide +kernel
theorem certified3059swap : Certified (graph core3059) (root 10) 4 0 :=
  of_native_maps core3059 DegreeTwoThreeSpectrum7352.graph DegreeTwoThreeSpectrum6527.graph
    sourceMap3059swap fusedMap3059swap sourceMap3059swap_checked fusedMap3059swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3059
#print axioms sourceMap3059swap_checked
#print axioms fusedMap3059swap_checked
#print axioms certified3059swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
