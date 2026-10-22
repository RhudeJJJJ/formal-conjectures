/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3853 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap3853 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3853 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3853_checked : acceptsGraphIso
    (source (graph core3853) (root 8) 1 4) DegreeTwoThreeSpectrum4200.graph sourceMap3853=true := by decide +kernel
theorem fusedMap3853_checked : acceptsGraphIso
    (fused (graph core3853) (root 8) 1 4) DegreeTwoThreeSpectrum3895.graph fusedMap3853=true := by decide +kernel
theorem certified3853 : Certified (graph core3853) (root 8) 1 4 :=
  of_native_maps core3853 DegreeTwoThreeSpectrum4200.graph DegreeTwoThreeSpectrum3895.graph
    sourceMap3853 fusedMap3853 sourceMap3853_checked fusedMap3853_checked
    DegreeTwoThreeFiniteComparisons.comparison3853
#print axioms sourceMap3853_checked
#print axioms fusedMap3853_checked
#print axioms certified3853
def sourceMap3853swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3853swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3853swap_checked : acceptsGraphIso
    (source (graph core3853) (root 8) 4 1) DegreeTwoThreeSpectrum4200.graph sourceMap3853swap=true := by decide +kernel
theorem fusedMap3853swap_checked : acceptsGraphIso
    (fused (graph core3853) (root 8) 4 1) DegreeTwoThreeSpectrum3895.graph fusedMap3853swap=true := by decide +kernel
theorem certified3853swap : Certified (graph core3853) (root 8) 4 1 :=
  of_native_maps core3853 DegreeTwoThreeSpectrum4200.graph DegreeTwoThreeSpectrum3895.graph
    sourceMap3853swap fusedMap3853swap sourceMap3853swap_checked fusedMap3853swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3853
#print axioms sourceMap3853swap_checked
#print axioms fusedMap3853swap_checked
#print axioms certified3853swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
