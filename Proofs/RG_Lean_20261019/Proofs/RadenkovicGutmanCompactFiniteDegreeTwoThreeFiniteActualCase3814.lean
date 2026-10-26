/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3814 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap3814 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3814 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3814_checked : acceptsGraphIso
    (source (graph core3814) (root 7) 1 4) DegreeTwoThreeSpectrum3248.graph sourceMap3814=true := by decide +kernel
theorem fusedMap3814_checked : acceptsGraphIso
    (fused (graph core3814) (root 7) 1 4) DegreeTwoThreeSpectrum2536.graph fusedMap3814=true := by decide +kernel
theorem certified3814 : Certified (graph core3814) (root 7) 1 4 :=
  of_native_maps core3814 DegreeTwoThreeSpectrum3248.graph DegreeTwoThreeSpectrum2536.graph
    sourceMap3814 fusedMap3814 sourceMap3814_checked fusedMap3814_checked
    DegreeTwoThreeFiniteComparisons.comparison3814
#print axioms sourceMap3814_checked
#print axioms fusedMap3814_checked
#print axioms certified3814
def sourceMap3814swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3814swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3814swap_checked : acceptsGraphIso
    (source (graph core3814) (root 7) 4 1) DegreeTwoThreeSpectrum3248.graph sourceMap3814swap=true := by decide +kernel
theorem fusedMap3814swap_checked : acceptsGraphIso
    (fused (graph core3814) (root 7) 4 1) DegreeTwoThreeSpectrum2536.graph fusedMap3814swap=true := by decide +kernel
theorem certified3814swap : Certified (graph core3814) (root 7) 4 1 :=
  of_native_maps core3814 DegreeTwoThreeSpectrum3248.graph DegreeTwoThreeSpectrum2536.graph
    sourceMap3814swap fusedMap3814swap sourceMap3814swap_checked fusedMap3814swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3814
#print axioms sourceMap3814swap_checked
#print axioms fusedMap3814swap_checked
#print axioms certified3814swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
