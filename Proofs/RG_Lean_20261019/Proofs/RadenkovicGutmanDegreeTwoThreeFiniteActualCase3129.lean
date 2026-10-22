/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3129 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap3129 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3129 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3129_checked : acceptsGraphIso
    (source (graph core3129) (root 7) 0 5) DegreeTwoThreeSpectrum2567.graph sourceMap3129=true := by decide +kernel
theorem fusedMap3129_checked : acceptsGraphIso
    (fused (graph core3129) (root 7) 0 5) DegreeTwoThreeSpectrum2569.graph fusedMap3129=true := by decide +kernel
theorem certified3129 : Certified (graph core3129) (root 7) 0 5 :=
  of_native_maps core3129 DegreeTwoThreeSpectrum2567.graph DegreeTwoThreeSpectrum2569.graph
    sourceMap3129 fusedMap3129 sourceMap3129_checked fusedMap3129_checked
    DegreeTwoThreeFiniteComparisons.comparison3129
#print axioms sourceMap3129_checked
#print axioms fusedMap3129_checked
#print axioms certified3129
def sourceMap3129swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3129swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3129swap_checked : acceptsGraphIso
    (source (graph core3129) (root 7) 5 0) DegreeTwoThreeSpectrum2567.graph sourceMap3129swap=true := by decide +kernel
theorem fusedMap3129swap_checked : acceptsGraphIso
    (fused (graph core3129) (root 7) 5 0) DegreeTwoThreeSpectrum2569.graph fusedMap3129swap=true := by decide +kernel
theorem certified3129swap : Certified (graph core3129) (root 7) 5 0 :=
  of_native_maps core3129 DegreeTwoThreeSpectrum2567.graph DegreeTwoThreeSpectrum2569.graph
    sourceMap3129swap fusedMap3129swap sourceMap3129swap_checked fusedMap3129swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3129
#print axioms sourceMap3129swap_checked
#print axioms fusedMap3129swap_checked
#print axioms certified3129swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
