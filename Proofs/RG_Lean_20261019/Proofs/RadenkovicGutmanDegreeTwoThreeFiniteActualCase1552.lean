/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1552 : Family 10 := level10.get ⟨460,by decide⟩
def sourceMap1552 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1552 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1552_checked : acceptsGraphIso
    (source (graph core1552) (root 10) 0 2) DegreeTwoThreeSpectrum2887.graph sourceMap1552=true := by decide +kernel
theorem fusedMap1552_checked : acceptsGraphIso
    (fused (graph core1552) (root 10) 0 2) DegreeTwoThreeSpectrum2988.graph fusedMap1552=true := by decide +kernel
theorem certified1552 : Certified (graph core1552) (root 10) 0 2 :=
  of_native_maps core1552 DegreeTwoThreeSpectrum2887.graph DegreeTwoThreeSpectrum2988.graph
    sourceMap1552 fusedMap1552 sourceMap1552_checked fusedMap1552_checked
    DegreeTwoThreeFiniteComparisons.comparison1552
#print axioms sourceMap1552_checked
#print axioms fusedMap1552_checked
#print axioms certified1552
def sourceMap1552swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1552swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1552swap_checked : acceptsGraphIso
    (source (graph core1552) (root 10) 2 0) DegreeTwoThreeSpectrum2887.graph sourceMap1552swap=true := by decide +kernel
theorem fusedMap1552swap_checked : acceptsGraphIso
    (fused (graph core1552) (root 10) 2 0) DegreeTwoThreeSpectrum2988.graph fusedMap1552swap=true := by decide +kernel
theorem certified1552swap : Certified (graph core1552) (root 10) 2 0 :=
  of_native_maps core1552 DegreeTwoThreeSpectrum2887.graph DegreeTwoThreeSpectrum2988.graph
    sourceMap1552swap fusedMap1552swap sourceMap1552swap_checked fusedMap1552swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1552
#print axioms sourceMap1552swap_checked
#print axioms fusedMap1552swap_checked
#print axioms certified1552swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
