/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1719 : Family 10 := level10.get ⟨930,by decide⟩
def sourceMap1719 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1719 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1719_checked : acceptsGraphIso
    (source (graph core1719) (root 10) 0 2) DegreeTwoThreeSpectrum3708.graph sourceMap1719=true := by decide +kernel
theorem fusedMap1719_checked : acceptsGraphIso
    (fused (graph core1719) (root 10) 0 2) DegreeTwoThreeSpectrum2947.graph fusedMap1719=true := by decide +kernel
theorem certified1719 : Certified (graph core1719) (root 10) 0 2 :=
  of_native_maps core1719 DegreeTwoThreeSpectrum3708.graph DegreeTwoThreeSpectrum2947.graph
    sourceMap1719 fusedMap1719 sourceMap1719_checked fusedMap1719_checked
    DegreeTwoThreeFiniteComparisons.comparison1719
#print axioms sourceMap1719_checked
#print axioms fusedMap1719_checked
#print axioms certified1719
def sourceMap1719swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1719swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1719swap_checked : acceptsGraphIso
    (source (graph core1719) (root 10) 2 0) DegreeTwoThreeSpectrum3708.graph sourceMap1719swap=true := by decide +kernel
theorem fusedMap1719swap_checked : acceptsGraphIso
    (fused (graph core1719) (root 10) 2 0) DegreeTwoThreeSpectrum2947.graph fusedMap1719swap=true := by decide +kernel
theorem certified1719swap : Certified (graph core1719) (root 10) 2 0 :=
  of_native_maps core1719 DegreeTwoThreeSpectrum3708.graph DegreeTwoThreeSpectrum2947.graph
    sourceMap1719swap fusedMap1719swap sourceMap1719swap_checked fusedMap1719swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1719
#print axioms sourceMap1719swap_checked
#print axioms fusedMap1719swap_checked
#print axioms certified1719swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
