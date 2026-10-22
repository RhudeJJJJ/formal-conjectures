/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1890 : Family 10 := level10.get ⟨1350,by decide⟩
def sourceMap1890 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1890 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1890_checked : acceptsGraphIso
    (source (graph core1890) (root 10) 0 2) DegreeTwoThreeSpectrum3539.graph sourceMap1890=true := by decide +kernel
theorem fusedMap1890_checked : acceptsGraphIso
    (fused (graph core1890) (root 10) 0 2) DegreeTwoThreeSpectrum3541.graph fusedMap1890=true := by decide +kernel
theorem certified1890 : Certified (graph core1890) (root 10) 0 2 :=
  of_native_maps core1890 DegreeTwoThreeSpectrum3539.graph DegreeTwoThreeSpectrum3541.graph
    sourceMap1890 fusedMap1890 sourceMap1890_checked fusedMap1890_checked
    DegreeTwoThreeFiniteComparisons.comparison1890
#print axioms sourceMap1890_checked
#print axioms fusedMap1890_checked
#print axioms certified1890
def sourceMap1890swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1890swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1890swap_checked : acceptsGraphIso
    (source (graph core1890) (root 10) 2 0) DegreeTwoThreeSpectrum3539.graph sourceMap1890swap=true := by decide +kernel
theorem fusedMap1890swap_checked : acceptsGraphIso
    (fused (graph core1890) (root 10) 2 0) DegreeTwoThreeSpectrum3541.graph fusedMap1890swap=true := by decide +kernel
theorem certified1890swap : Certified (graph core1890) (root 10) 2 0 :=
  of_native_maps core1890 DegreeTwoThreeSpectrum3539.graph DegreeTwoThreeSpectrum3541.graph
    sourceMap1890swap fusedMap1890swap sourceMap1890swap_checked fusedMap1890swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1890
#print axioms sourceMap1890swap_checked
#print axioms fusedMap1890swap_checked
#print axioms certified1890swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
