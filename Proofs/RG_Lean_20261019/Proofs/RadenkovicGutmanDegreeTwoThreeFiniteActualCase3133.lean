/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3133 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap3133 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3133 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3133_checked : acceptsGraphIso
    (source (graph core3133) (root 7) 0 5) DegreeTwoThreeSpectrum2704.graph sourceMap3133=true := by decide +kernel
theorem fusedMap3133_checked : acceptsGraphIso
    (fused (graph core3133) (root 7) 0 5) DegreeTwoThreeSpectrum2706.graph fusedMap3133=true := by decide +kernel
theorem certified3133 : Certified (graph core3133) (root 7) 0 5 :=
  of_native_maps core3133 DegreeTwoThreeSpectrum2704.graph DegreeTwoThreeSpectrum2706.graph
    sourceMap3133 fusedMap3133 sourceMap3133_checked fusedMap3133_checked
    DegreeTwoThreeFiniteComparisons.comparison3133
#print axioms sourceMap3133_checked
#print axioms fusedMap3133_checked
#print axioms certified3133
def sourceMap3133swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3133swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3133swap_checked : acceptsGraphIso
    (source (graph core3133) (root 7) 5 0) DegreeTwoThreeSpectrum2704.graph sourceMap3133swap=true := by decide +kernel
theorem fusedMap3133swap_checked : acceptsGraphIso
    (fused (graph core3133) (root 7) 5 0) DegreeTwoThreeSpectrum2706.graph fusedMap3133swap=true := by decide +kernel
theorem certified3133swap : Certified (graph core3133) (root 7) 5 0 :=
  of_native_maps core3133 DegreeTwoThreeSpectrum2704.graph DegreeTwoThreeSpectrum2706.graph
    sourceMap3133swap fusedMap3133swap sourceMap3133swap_checked fusedMap3133swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3133
#print axioms sourceMap3133swap_checked
#print axioms fusedMap3133swap_checked
#print axioms certified3133swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
