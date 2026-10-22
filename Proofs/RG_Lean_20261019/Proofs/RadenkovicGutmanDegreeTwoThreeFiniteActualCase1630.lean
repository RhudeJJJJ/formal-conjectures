/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1630 : Family 10 := level10.get ⟨686,by decide⟩
def sourceMap1630 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1630 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1630_checked : acceptsGraphIso
    (source (graph core1630) (root 10) 0 2) DegreeTwoThreeSpectrum3387.graph sourceMap1630=true := by decide +kernel
theorem fusedMap1630_checked : acceptsGraphIso
    (fused (graph core1630) (root 10) 0 2) DegreeTwoThreeSpectrum2647.graph fusedMap1630=true := by decide +kernel
theorem certified1630 : Certified (graph core1630) (root 10) 0 2 :=
  of_native_maps core1630 DegreeTwoThreeSpectrum3387.graph DegreeTwoThreeSpectrum2647.graph
    sourceMap1630 fusedMap1630 sourceMap1630_checked fusedMap1630_checked
    DegreeTwoThreeFiniteComparisons.comparison1630
#print axioms sourceMap1630_checked
#print axioms fusedMap1630_checked
#print axioms certified1630
def sourceMap1630swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1630swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1630swap_checked : acceptsGraphIso
    (source (graph core1630) (root 10) 2 0) DegreeTwoThreeSpectrum3387.graph sourceMap1630swap=true := by decide +kernel
theorem fusedMap1630swap_checked : acceptsGraphIso
    (fused (graph core1630) (root 10) 2 0) DegreeTwoThreeSpectrum2647.graph fusedMap1630swap=true := by decide +kernel
theorem certified1630swap : Certified (graph core1630) (root 10) 2 0 :=
  of_native_maps core1630 DegreeTwoThreeSpectrum3387.graph DegreeTwoThreeSpectrum2647.graph
    sourceMap1630swap fusedMap1630swap sourceMap1630swap_checked fusedMap1630swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1630
#print axioms sourceMap1630swap_checked
#print axioms fusedMap1630swap_checked
#print axioms certified1630swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
