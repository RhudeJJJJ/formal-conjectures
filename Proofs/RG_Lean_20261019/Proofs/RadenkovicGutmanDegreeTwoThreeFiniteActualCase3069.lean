/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3069 : Family 10 := level10.get ⟨1768,by decide⟩
def sourceMap3069 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3069 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3069_checked : acceptsGraphIso
    (source (graph core3069) (root 10) 0 4) DegreeTwoThreeSpectrum7436.graph sourceMap3069=true := by decide +kernel
theorem fusedMap3069_checked : acceptsGraphIso
    (fused (graph core3069) (root 10) 0 4) DegreeTwoThreeSpectrum6685.graph fusedMap3069=true := by decide +kernel
theorem certified3069 : Certified (graph core3069) (root 10) 0 4 :=
  of_native_maps core3069 DegreeTwoThreeSpectrum7436.graph DegreeTwoThreeSpectrum6685.graph
    sourceMap3069 fusedMap3069 sourceMap3069_checked fusedMap3069_checked
    DegreeTwoThreeFiniteComparisons.comparison3069
#print axioms sourceMap3069_checked
#print axioms fusedMap3069_checked
#print axioms certified3069
def sourceMap3069swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3069swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3069swap_checked : acceptsGraphIso
    (source (graph core3069) (root 10) 4 0) DegreeTwoThreeSpectrum7436.graph sourceMap3069swap=true := by decide +kernel
theorem fusedMap3069swap_checked : acceptsGraphIso
    (fused (graph core3069) (root 10) 4 0) DegreeTwoThreeSpectrum6685.graph fusedMap3069swap=true := by decide +kernel
theorem certified3069swap : Certified (graph core3069) (root 10) 4 0 :=
  of_native_maps core3069 DegreeTwoThreeSpectrum7436.graph DegreeTwoThreeSpectrum6685.graph
    sourceMap3069swap fusedMap3069swap sourceMap3069swap_checked fusedMap3069swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3069
#print axioms sourceMap3069swap_checked
#print axioms fusedMap3069swap_checked
#print axioms certified3069swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
