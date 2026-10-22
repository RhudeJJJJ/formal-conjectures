/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2609 : Family 10 := level10.get ⟨556,by decide⟩
def sourceMap2609 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2609 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2609_checked : acceptsGraphIso
    (source (graph core2609) (root 10) 0 4) DegreeTwoThreeSpectrum6171.graph sourceMap2609=true := by decide +kernel
theorem fusedMap2609_checked : acceptsGraphIso
    (fused (graph core2609) (root 10) 0 4) DegreeTwoThreeSpectrum5214.graph fusedMap2609=true := by decide +kernel
theorem certified2609 : Certified (graph core2609) (root 10) 0 4 :=
  of_native_maps core2609 DegreeTwoThreeSpectrum6171.graph DegreeTwoThreeSpectrum5214.graph
    sourceMap2609 fusedMap2609 sourceMap2609_checked fusedMap2609_checked
    DegreeTwoThreeFiniteComparisons.comparison2609
#print axioms sourceMap2609_checked
#print axioms fusedMap2609_checked
#print axioms certified2609
def sourceMap2609swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2609swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2609swap_checked : acceptsGraphIso
    (source (graph core2609) (root 10) 4 0) DegreeTwoThreeSpectrum6171.graph sourceMap2609swap=true := by decide +kernel
theorem fusedMap2609swap_checked : acceptsGraphIso
    (fused (graph core2609) (root 10) 4 0) DegreeTwoThreeSpectrum5214.graph fusedMap2609swap=true := by decide +kernel
theorem certified2609swap : Certified (graph core2609) (root 10) 4 0 :=
  of_native_maps core2609 DegreeTwoThreeSpectrum6171.graph DegreeTwoThreeSpectrum5214.graph
    sourceMap2609swap fusedMap2609swap sourceMap2609swap_checked fusedMap2609swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2609
#print axioms sourceMap2609swap_checked
#print axioms fusedMap2609swap_checked
#print axioms certified2609swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
