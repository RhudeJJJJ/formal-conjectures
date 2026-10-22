/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1926 : Family 10 := level10.get ⟨1433,by decide⟩
def sourceMap1926 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,4,5,6,7,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1926 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1926_checked : acceptsGraphIso
    (source (graph core1926) (root 10) 0 2) DegreeTwoThreeSpectrum3654.graph sourceMap1926=true := by decide +kernel
theorem fusedMap1926_checked : acceptsGraphIso
    (fused (graph core1926) (root 10) 0 2) DegreeTwoThreeSpectrum3665.graph fusedMap1926=true := by decide +kernel
theorem certified1926 : Certified (graph core1926) (root 10) 0 2 :=
  of_native_maps core1926 DegreeTwoThreeSpectrum3654.graph DegreeTwoThreeSpectrum3665.graph
    sourceMap1926 fusedMap1926 sourceMap1926_checked fusedMap1926_checked
    DegreeTwoThreeFiniteComparisons.comparison1926
#print axioms sourceMap1926_checked
#print axioms fusedMap1926_checked
#print axioms certified1926
def sourceMap1926swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,4,5,6,1,2,3,7] (sourceLabel 10 2 0 v)
def fusedMap1926swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1926swap_checked : acceptsGraphIso
    (source (graph core1926) (root 10) 2 0) DegreeTwoThreeSpectrum3654.graph sourceMap1926swap=true := by decide +kernel
theorem fusedMap1926swap_checked : acceptsGraphIso
    (fused (graph core1926) (root 10) 2 0) DegreeTwoThreeSpectrum3665.graph fusedMap1926swap=true := by decide +kernel
theorem certified1926swap : Certified (graph core1926) (root 10) 2 0 :=
  of_native_maps core1926 DegreeTwoThreeSpectrum3654.graph DegreeTwoThreeSpectrum3665.graph
    sourceMap1926swap fusedMap1926swap sourceMap1926swap_checked fusedMap1926swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1926
#print axioms sourceMap1926swap_checked
#print axioms fusedMap1926swap_checked
#print axioms certified1926swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
