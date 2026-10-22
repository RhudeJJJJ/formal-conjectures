/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1618 : Family 10 := level10.get ⟨657,by decide⟩
def sourceMap1618 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1618 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1618_checked : acceptsGraphIso
    (source (graph core1618) (root 10) 0 2) DegreeTwoThreeSpectrum3365.graph sourceMap1618=true := by decide +kernel
theorem fusedMap1618_checked : acceptsGraphIso
    (fused (graph core1618) (root 10) 0 2) DegreeTwoThreeSpectrum2604.graph fusedMap1618=true := by decide +kernel
theorem certified1618 : Certified (graph core1618) (root 10) 0 2 :=
  of_native_maps core1618 DegreeTwoThreeSpectrum3365.graph DegreeTwoThreeSpectrum2604.graph
    sourceMap1618 fusedMap1618 sourceMap1618_checked fusedMap1618_checked
    DegreeTwoThreeFiniteComparisons.comparison1618
#print axioms sourceMap1618_checked
#print axioms fusedMap1618_checked
#print axioms certified1618
def sourceMap1618swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1618swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1618swap_checked : acceptsGraphIso
    (source (graph core1618) (root 10) 2 0) DegreeTwoThreeSpectrum3365.graph sourceMap1618swap=true := by decide +kernel
theorem fusedMap1618swap_checked : acceptsGraphIso
    (fused (graph core1618) (root 10) 2 0) DegreeTwoThreeSpectrum2604.graph fusedMap1618swap=true := by decide +kernel
theorem certified1618swap : Certified (graph core1618) (root 10) 2 0 :=
  of_native_maps core1618 DegreeTwoThreeSpectrum3365.graph DegreeTwoThreeSpectrum2604.graph
    sourceMap1618swap fusedMap1618swap sourceMap1618swap_checked fusedMap1618swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1618
#print axioms sourceMap1618swap_checked
#print axioms fusedMap1618swap_checked
#print axioms certified1618swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
