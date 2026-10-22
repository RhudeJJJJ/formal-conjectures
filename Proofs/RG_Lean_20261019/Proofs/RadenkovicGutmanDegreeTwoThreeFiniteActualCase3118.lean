/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3118 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap3118 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3118 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3118_checked : acceptsGraphIso
    (source (graph core3118) (root 7) 0 5) DegreeTwoThreeSpectrum2888.graph sourceMap3118=true := by decide +kernel
theorem fusedMap3118_checked : acceptsGraphIso
    (fused (graph core3118) (root 7) 0 5) DegreeTwoThreeSpectrum2388.graph fusedMap3118=true := by decide +kernel
theorem certified3118 : Certified (graph core3118) (root 7) 0 5 :=
  of_native_maps core3118 DegreeTwoThreeSpectrum2888.graph DegreeTwoThreeSpectrum2388.graph
    sourceMap3118 fusedMap3118 sourceMap3118_checked fusedMap3118_checked
    DegreeTwoThreeFiniteComparisons.comparison3118
#print axioms sourceMap3118_checked
#print axioms fusedMap3118_checked
#print axioms certified3118
def sourceMap3118swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3118swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3118swap_checked : acceptsGraphIso
    (source (graph core3118) (root 7) 5 0) DegreeTwoThreeSpectrum2888.graph sourceMap3118swap=true := by decide +kernel
theorem fusedMap3118swap_checked : acceptsGraphIso
    (fused (graph core3118) (root 7) 5 0) DegreeTwoThreeSpectrum2388.graph fusedMap3118swap=true := by decide +kernel
theorem certified3118swap : Certified (graph core3118) (root 7) 5 0 :=
  of_native_maps core3118 DegreeTwoThreeSpectrum2888.graph DegreeTwoThreeSpectrum2388.graph
    sourceMap3118swap fusedMap3118swap sourceMap3118swap_checked fusedMap3118swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3118
#print axioms sourceMap3118swap_checked
#print axioms fusedMap3118swap_checked
#print axioms certified3118swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
