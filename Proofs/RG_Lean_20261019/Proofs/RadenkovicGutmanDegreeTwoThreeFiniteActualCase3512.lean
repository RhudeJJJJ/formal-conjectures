/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3512 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap3512 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3512 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3512_checked : acceptsGraphIso
    (source (graph core3512) (root 7) 0 6) DegreeTwoThreeSpectrum3993.graph sourceMap3512=true := by decide +kernel
theorem fusedMap3512_checked : acceptsGraphIso
    (fused (graph core3512) (root 7) 0 6) DegreeTwoThreeSpectrum3995.graph fusedMap3512=true := by decide +kernel
theorem certified3512 : Certified (graph core3512) (root 7) 0 6 :=
  of_native_maps core3512 DegreeTwoThreeSpectrum3993.graph DegreeTwoThreeSpectrum3995.graph
    sourceMap3512 fusedMap3512 sourceMap3512_checked fusedMap3512_checked
    DegreeTwoThreeFiniteComparisons.comparison3512
#print axioms sourceMap3512_checked
#print axioms fusedMap3512_checked
#print axioms certified3512
def sourceMap3512swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3512swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3512swap_checked : acceptsGraphIso
    (source (graph core3512) (root 7) 6 0) DegreeTwoThreeSpectrum3993.graph sourceMap3512swap=true := by decide +kernel
theorem fusedMap3512swap_checked : acceptsGraphIso
    (fused (graph core3512) (root 7) 6 0) DegreeTwoThreeSpectrum3995.graph fusedMap3512swap=true := by decide +kernel
theorem certified3512swap : Certified (graph core3512) (root 7) 6 0 :=
  of_native_maps core3512 DegreeTwoThreeSpectrum3993.graph DegreeTwoThreeSpectrum3995.graph
    sourceMap3512swap fusedMap3512swap sourceMap3512swap_checked fusedMap3512swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3512
#print axioms sourceMap3512swap_checked
#print axioms fusedMap3512swap_checked
#print axioms certified3512swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
