/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1775 : Family 10 := level10.get ⟨1074,by decide⟩
def sourceMap1775 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1775 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1775_checked : acceptsGraphIso
    (source (graph core1775) (root 10) 0 2) DegreeTwoThreeSpectrum3127.graph sourceMap1775=true := by decide +kernel
theorem fusedMap1775_checked : acceptsGraphIso
    (fused (graph core1775) (root 10) 0 2) DegreeTwoThreeSpectrum3128.graph fusedMap1775=true := by decide +kernel
theorem certified1775 : Certified (graph core1775) (root 10) 0 2 :=
  of_native_maps core1775 DegreeTwoThreeSpectrum3127.graph DegreeTwoThreeSpectrum3128.graph
    sourceMap1775 fusedMap1775 sourceMap1775_checked fusedMap1775_checked
    DegreeTwoThreeFiniteComparisons.comparison1775
#print axioms sourceMap1775_checked
#print axioms fusedMap1775_checked
#print axioms certified1775
def sourceMap1775swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1775swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1775swap_checked : acceptsGraphIso
    (source (graph core1775) (root 10) 2 0) DegreeTwoThreeSpectrum3127.graph sourceMap1775swap=true := by decide +kernel
theorem fusedMap1775swap_checked : acceptsGraphIso
    (fused (graph core1775) (root 10) 2 0) DegreeTwoThreeSpectrum3128.graph fusedMap1775swap=true := by decide +kernel
theorem certified1775swap : Certified (graph core1775) (root 10) 2 0 :=
  of_native_maps core1775 DegreeTwoThreeSpectrum3127.graph DegreeTwoThreeSpectrum3128.graph
    sourceMap1775swap fusedMap1775swap sourceMap1775swap_checked fusedMap1775swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1775
#print axioms sourceMap1775swap_checked
#print axioms fusedMap1775swap_checked
#print axioms certified1775swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
