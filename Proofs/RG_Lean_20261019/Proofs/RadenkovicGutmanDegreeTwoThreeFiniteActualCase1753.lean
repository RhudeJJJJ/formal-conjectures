/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1753 : Family 10 := level10.get ⟨1014,by decide⟩
def sourceMap1753 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1753 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1753_checked : acceptsGraphIso
    (source (graph core1753) (root 10) 0 2) DegreeTwoThreeSpectrum3031.graph sourceMap1753=true := by decide +kernel
theorem fusedMap1753_checked : acceptsGraphIso
    (fused (graph core1753) (root 10) 0 2) DegreeTwoThreeSpectrum3032.graph fusedMap1753=true := by decide +kernel
theorem certified1753 : Certified (graph core1753) (root 10) 0 2 :=
  of_native_maps core1753 DegreeTwoThreeSpectrum3031.graph DegreeTwoThreeSpectrum3032.graph
    sourceMap1753 fusedMap1753 sourceMap1753_checked fusedMap1753_checked
    DegreeTwoThreeFiniteComparisons.comparison1753
#print axioms sourceMap1753_checked
#print axioms fusedMap1753_checked
#print axioms certified1753
def sourceMap1753swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1753swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1753swap_checked : acceptsGraphIso
    (source (graph core1753) (root 10) 2 0) DegreeTwoThreeSpectrum3031.graph sourceMap1753swap=true := by decide +kernel
theorem fusedMap1753swap_checked : acceptsGraphIso
    (fused (graph core1753) (root 10) 2 0) DegreeTwoThreeSpectrum3032.graph fusedMap1753swap=true := by decide +kernel
theorem certified1753swap : Certified (graph core1753) (root 10) 2 0 :=
  of_native_maps core1753 DegreeTwoThreeSpectrum3031.graph DegreeTwoThreeSpectrum3032.graph
    sourceMap1753swap fusedMap1753swap sourceMap1753swap_checked fusedMap1753swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1753
#print axioms sourceMap1753swap_checked
#print axioms fusedMap1753swap_checked
#print axioms certified1753swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
