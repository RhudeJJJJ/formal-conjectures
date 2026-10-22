/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1841 : Family 10 := level10.get ⟨1226,by decide⟩
def sourceMap1841 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1841 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1841_checked : acceptsGraphIso
    (source (graph core1841) (root 10) 0 2) DegreeTwoThreeSpectrum3238.graph sourceMap1841=true := by decide +kernel
theorem fusedMap1841_checked : acceptsGraphIso
    (fused (graph core1841) (root 10) 0 2) DegreeTwoThreeSpectrum3372.graph fusedMap1841=true := by decide +kernel
theorem certified1841 : Certified (graph core1841) (root 10) 0 2 :=
  of_native_maps core1841 DegreeTwoThreeSpectrum3238.graph DegreeTwoThreeSpectrum3372.graph
    sourceMap1841 fusedMap1841 sourceMap1841_checked fusedMap1841_checked
    DegreeTwoThreeFiniteComparisons.comparison1841
#print axioms sourceMap1841_checked
#print axioms fusedMap1841_checked
#print axioms certified1841
def sourceMap1841swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1841swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1841swap_checked : acceptsGraphIso
    (source (graph core1841) (root 10) 2 0) DegreeTwoThreeSpectrum3238.graph sourceMap1841swap=true := by decide +kernel
theorem fusedMap1841swap_checked : acceptsGraphIso
    (fused (graph core1841) (root 10) 2 0) DegreeTwoThreeSpectrum3372.graph fusedMap1841swap=true := by decide +kernel
theorem certified1841swap : Certified (graph core1841) (root 10) 2 0 :=
  of_native_maps core1841 DegreeTwoThreeSpectrum3238.graph DegreeTwoThreeSpectrum3372.graph
    sourceMap1841swap fusedMap1841swap sourceMap1841swap_checked fusedMap1841swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1841
#print axioms sourceMap1841swap_checked
#print axioms fusedMap1841swap_checked
#print axioms certified1841swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
