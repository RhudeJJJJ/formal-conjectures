/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1568 : Family 10 := level10.get ⟨501,by decide⟩
def sourceMap1568 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1568 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1568_checked : acceptsGraphIso
    (source (graph core1568) (root 10) 0 2) DegreeTwoThreeSpectrum3018.graph sourceMap1568=true := by decide +kernel
theorem fusedMap1568_checked : acceptsGraphIso
    (fused (graph core1568) (root 10) 0 2) DegreeTwoThreeSpectrum2439.graph fusedMap1568=true := by decide +kernel
theorem certified1568 : Certified (graph core1568) (root 10) 0 2 :=
  of_native_maps core1568 DegreeTwoThreeSpectrum3018.graph DegreeTwoThreeSpectrum2439.graph
    sourceMap1568 fusedMap1568 sourceMap1568_checked fusedMap1568_checked
    DegreeTwoThreeFiniteComparisons.comparison1568
#print axioms sourceMap1568_checked
#print axioms fusedMap1568_checked
#print axioms certified1568
def sourceMap1568swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1568swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1568swap_checked : acceptsGraphIso
    (source (graph core1568) (root 10) 2 0) DegreeTwoThreeSpectrum3018.graph sourceMap1568swap=true := by decide +kernel
theorem fusedMap1568swap_checked : acceptsGraphIso
    (fused (graph core1568) (root 10) 2 0) DegreeTwoThreeSpectrum2439.graph fusedMap1568swap=true := by decide +kernel
theorem certified1568swap : Certified (graph core1568) (root 10) 2 0 :=
  of_native_maps core1568 DegreeTwoThreeSpectrum3018.graph DegreeTwoThreeSpectrum2439.graph
    sourceMap1568swap fusedMap1568swap sourceMap1568swap_checked fusedMap1568swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1568
#print axioms sourceMap1568swap_checked
#print axioms fusedMap1568swap_checked
#print axioms certified1568swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
