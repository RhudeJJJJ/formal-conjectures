/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1510 : Family 10 := level10.get ⟨328,by decide⟩
def sourceMap1510 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1510 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1510_checked : acceptsGraphIso
    (source (graph core1510) (root 10) 0 2) DegreeTwoThreeSpectrum2745.graph sourceMap1510=true := by decide +kernel
theorem fusedMap1510_checked : acceptsGraphIso
    (fused (graph core1510) (root 10) 0 2) DegreeTwoThreeSpectrum2747.graph fusedMap1510=true := by decide +kernel
theorem certified1510 : Certified (graph core1510) (root 10) 0 2 :=
  of_native_maps core1510 DegreeTwoThreeSpectrum2745.graph DegreeTwoThreeSpectrum2747.graph
    sourceMap1510 fusedMap1510 sourceMap1510_checked fusedMap1510_checked
    DegreeTwoThreeFiniteComparisons.comparison1510
#print axioms sourceMap1510_checked
#print axioms fusedMap1510_checked
#print axioms certified1510
def sourceMap1510swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1510swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1510swap_checked : acceptsGraphIso
    (source (graph core1510) (root 10) 2 0) DegreeTwoThreeSpectrum2745.graph sourceMap1510swap=true := by decide +kernel
theorem fusedMap1510swap_checked : acceptsGraphIso
    (fused (graph core1510) (root 10) 2 0) DegreeTwoThreeSpectrum2747.graph fusedMap1510swap=true := by decide +kernel
theorem certified1510swap : Certified (graph core1510) (root 10) 2 0 :=
  of_native_maps core1510 DegreeTwoThreeSpectrum2745.graph DegreeTwoThreeSpectrum2747.graph
    sourceMap1510swap fusedMap1510swap sourceMap1510swap_checked fusedMap1510swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1510
#print axioms sourceMap1510swap_checked
#print axioms fusedMap1510swap_checked
#print axioms certified1510swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
