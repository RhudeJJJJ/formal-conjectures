/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1445 : Family 10 := level10.get ⟨84,by decide⟩
def sourceMap1445 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1445 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1445_checked : acceptsGraphIso
    (source (graph core1445) (root 10) 0 2) DegreeTwoThreeSpectrum2633.graph sourceMap1445=true := by decide +kernel
theorem fusedMap1445_checked : acceptsGraphIso
    (fused (graph core1445) (root 10) 0 2) DegreeTwoThreeSpectrum2345.graph fusedMap1445=true := by decide +kernel
theorem certified1445 : Certified (graph core1445) (root 10) 0 2 :=
  of_native_maps core1445 DegreeTwoThreeSpectrum2633.graph DegreeTwoThreeSpectrum2345.graph
    sourceMap1445 fusedMap1445 sourceMap1445_checked fusedMap1445_checked
    DegreeTwoThreeFiniteComparisons.comparison1445
#print axioms sourceMap1445_checked
#print axioms fusedMap1445_checked
#print axioms certified1445
def sourceMap1445swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1445swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1445swap_checked : acceptsGraphIso
    (source (graph core1445) (root 10) 2 0) DegreeTwoThreeSpectrum2633.graph sourceMap1445swap=true := by decide +kernel
theorem fusedMap1445swap_checked : acceptsGraphIso
    (fused (graph core1445) (root 10) 2 0) DegreeTwoThreeSpectrum2345.graph fusedMap1445swap=true := by decide +kernel
theorem certified1445swap : Certified (graph core1445) (root 10) 2 0 :=
  of_native_maps core1445 DegreeTwoThreeSpectrum2633.graph DegreeTwoThreeSpectrum2345.graph
    sourceMap1445swap fusedMap1445swap sourceMap1445swap_checked fusedMap1445swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1445
#print axioms sourceMap1445swap_checked
#print axioms fusedMap1445swap_checked
#print axioms certified1445swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
