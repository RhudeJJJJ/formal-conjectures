/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1657 : Family 10 := level10.get ⟨766,by decide⟩
def sourceMap1657 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1657 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1657_checked : acceptsGraphIso
    (source (graph core1657) (root 10) 0 2) DegreeTwoThreeSpectrum3540.graph sourceMap1657=true := by decide +kernel
theorem fusedMap1657_checked : acceptsGraphIso
    (fused (graph core1657) (root 10) 0 2) DegreeTwoThreeSpectrum2733.graph fusedMap1657=true := by decide +kernel
theorem certified1657 : Certified (graph core1657) (root 10) 0 2 :=
  of_native_maps core1657 DegreeTwoThreeSpectrum3540.graph DegreeTwoThreeSpectrum2733.graph
    sourceMap1657 fusedMap1657 sourceMap1657_checked fusedMap1657_checked
    DegreeTwoThreeFiniteComparisons.comparison1657
#print axioms sourceMap1657_checked
#print axioms fusedMap1657_checked
#print axioms certified1657
def sourceMap1657swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1657swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1657swap_checked : acceptsGraphIso
    (source (graph core1657) (root 10) 2 0) DegreeTwoThreeSpectrum3540.graph sourceMap1657swap=true := by decide +kernel
theorem fusedMap1657swap_checked : acceptsGraphIso
    (fused (graph core1657) (root 10) 2 0) DegreeTwoThreeSpectrum2733.graph fusedMap1657swap=true := by decide +kernel
theorem certified1657swap : Certified (graph core1657) (root 10) 2 0 :=
  of_native_maps core1657 DegreeTwoThreeSpectrum3540.graph DegreeTwoThreeSpectrum2733.graph
    sourceMap1657swap fusedMap1657swap sourceMap1657swap_checked fusedMap1657swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1657
#print axioms sourceMap1657swap_checked
#print axioms fusedMap1657swap_checked
#print axioms certified1657swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
