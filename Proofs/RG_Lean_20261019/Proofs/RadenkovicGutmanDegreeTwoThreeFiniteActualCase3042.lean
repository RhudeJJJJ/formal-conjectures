/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3042 : Family 10 := level10.get ⟨1665,by decide⟩
def sourceMap3042 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3042 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3042_checked : acceptsGraphIso
    (source (graph core3042) (root 10) 0 4) DegreeTwoThreeSpectrum7230.graph sourceMap3042=true := by decide +kernel
theorem fusedMap3042_checked : acceptsGraphIso
    (fused (graph core3042) (root 10) 0 4) DegreeTwoThreeSpectrum6282.graph fusedMap3042=true := by decide +kernel
theorem certified3042 : Certified (graph core3042) (root 10) 0 4 :=
  of_native_maps core3042 DegreeTwoThreeSpectrum7230.graph DegreeTwoThreeSpectrum6282.graph
    sourceMap3042 fusedMap3042 sourceMap3042_checked fusedMap3042_checked
    DegreeTwoThreeFiniteComparisons.comparison3042
#print axioms sourceMap3042_checked
#print axioms fusedMap3042_checked
#print axioms certified3042
def sourceMap3042swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3042swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3042swap_checked : acceptsGraphIso
    (source (graph core3042) (root 10) 4 0) DegreeTwoThreeSpectrum7230.graph sourceMap3042swap=true := by decide +kernel
theorem fusedMap3042swap_checked : acceptsGraphIso
    (fused (graph core3042) (root 10) 4 0) DegreeTwoThreeSpectrum6282.graph fusedMap3042swap=true := by decide +kernel
theorem certified3042swap : Certified (graph core3042) (root 10) 4 0 :=
  of_native_maps core3042 DegreeTwoThreeSpectrum7230.graph DegreeTwoThreeSpectrum6282.graph
    sourceMap3042swap fusedMap3042swap sourceMap3042swap_checked fusedMap3042swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3042
#print axioms sourceMap3042swap_checked
#print axioms fusedMap3042swap_checked
#print axioms certified3042swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
