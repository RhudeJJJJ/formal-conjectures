/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1594 : Family 10 := level10.get ⟨587,by decide⟩
def sourceMap1594 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1594 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1594_checked : acceptsGraphIso
    (source (graph core1594) (root 10) 0 2) DegreeTwoThreeSpectrum3232.graph sourceMap1594=true := by decide +kernel
theorem fusedMap1594_checked : acceptsGraphIso
    (fused (graph core1594) (root 10) 0 2) DegreeTwoThreeSpectrum2527.graph fusedMap1594=true := by decide +kernel
theorem certified1594 : Certified (graph core1594) (root 10) 0 2 :=
  of_native_maps core1594 DegreeTwoThreeSpectrum3232.graph DegreeTwoThreeSpectrum2527.graph
    sourceMap1594 fusedMap1594 sourceMap1594_checked fusedMap1594_checked
    DegreeTwoThreeFiniteComparisons.comparison1594
#print axioms sourceMap1594_checked
#print axioms fusedMap1594_checked
#print axioms certified1594
def sourceMap1594swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1594swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1594swap_checked : acceptsGraphIso
    (source (graph core1594) (root 10) 2 0) DegreeTwoThreeSpectrum3232.graph sourceMap1594swap=true := by decide +kernel
theorem fusedMap1594swap_checked : acceptsGraphIso
    (fused (graph core1594) (root 10) 2 0) DegreeTwoThreeSpectrum2527.graph fusedMap1594swap=true := by decide +kernel
theorem certified1594swap : Certified (graph core1594) (root 10) 2 0 :=
  of_native_maps core1594 DegreeTwoThreeSpectrum3232.graph DegreeTwoThreeSpectrum2527.graph
    sourceMap1594swap fusedMap1594swap sourceMap1594swap_checked fusedMap1594swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1594
#print axioms sourceMap1594swap_checked
#print axioms fusedMap1594swap_checked
#print axioms certified1594swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
