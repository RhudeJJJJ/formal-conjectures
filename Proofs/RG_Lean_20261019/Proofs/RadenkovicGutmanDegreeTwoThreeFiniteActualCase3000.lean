/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3000 : Family 10 := level10.get ⟨1570,by decide⟩
def sourceMap3000 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3000 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3000_checked : acceptsGraphIso
    (source (graph core3000) (root 10) 0 4) DegreeTwoThreeSpectrum7110.graph sourceMap3000=true := by decide +kernel
theorem fusedMap3000_checked : acceptsGraphIso
    (fused (graph core3000) (root 10) 0 4) DegreeTwoThreeSpectrum6048.graph fusedMap3000=true := by decide +kernel
theorem certified3000 : Certified (graph core3000) (root 10) 0 4 :=
  of_native_maps core3000 DegreeTwoThreeSpectrum7110.graph DegreeTwoThreeSpectrum6048.graph
    sourceMap3000 fusedMap3000 sourceMap3000_checked fusedMap3000_checked
    DegreeTwoThreeFiniteComparisons.comparison3000
#print axioms sourceMap3000_checked
#print axioms fusedMap3000_checked
#print axioms certified3000
def sourceMap3000swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3000swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3000swap_checked : acceptsGraphIso
    (source (graph core3000) (root 10) 4 0) DegreeTwoThreeSpectrum7110.graph sourceMap3000swap=true := by decide +kernel
theorem fusedMap3000swap_checked : acceptsGraphIso
    (fused (graph core3000) (root 10) 4 0) DegreeTwoThreeSpectrum6048.graph fusedMap3000swap=true := by decide +kernel
theorem certified3000swap : Certified (graph core3000) (root 10) 4 0 :=
  of_native_maps core3000 DegreeTwoThreeSpectrum7110.graph DegreeTwoThreeSpectrum6048.graph
    sourceMap3000swap fusedMap3000swap sourceMap3000swap_checked fusedMap3000swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3000
#print axioms sourceMap3000swap_checked
#print axioms fusedMap3000swap_checked
#print axioms certified3000swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
