/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1639 : Family 10 := level10.get ⟨716,by decide⟩
def sourceMap1639 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1639 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1639_checked : acceptsGraphIso
    (source (graph core1639) (root 10) 0 2) DegreeTwoThreeSpectrum3452.graph sourceMap1639=true := by decide +kernel
theorem fusedMap1639_checked : acceptsGraphIso
    (fused (graph core1639) (root 10) 0 2) DegreeTwoThreeSpectrum2675.graph fusedMap1639=true := by decide +kernel
theorem certified1639 : Certified (graph core1639) (root 10) 0 2 :=
  of_native_maps core1639 DegreeTwoThreeSpectrum3452.graph DegreeTwoThreeSpectrum2675.graph
    sourceMap1639 fusedMap1639 sourceMap1639_checked fusedMap1639_checked
    DegreeTwoThreeFiniteComparisons.comparison1639
#print axioms sourceMap1639_checked
#print axioms fusedMap1639_checked
#print axioms certified1639
def sourceMap1639swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1639swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1639swap_checked : acceptsGraphIso
    (source (graph core1639) (root 10) 2 0) DegreeTwoThreeSpectrum3452.graph sourceMap1639swap=true := by decide +kernel
theorem fusedMap1639swap_checked : acceptsGraphIso
    (fused (graph core1639) (root 10) 2 0) DegreeTwoThreeSpectrum2675.graph fusedMap1639swap=true := by decide +kernel
theorem certified1639swap : Certified (graph core1639) (root 10) 2 0 :=
  of_native_maps core1639 DegreeTwoThreeSpectrum3452.graph DegreeTwoThreeSpectrum2675.graph
    sourceMap1639swap fusedMap1639swap sourceMap1639swap_checked fusedMap1639swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1639
#print axioms sourceMap1639swap_checked
#print axioms fusedMap1639swap_checked
#print axioms certified1639swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
