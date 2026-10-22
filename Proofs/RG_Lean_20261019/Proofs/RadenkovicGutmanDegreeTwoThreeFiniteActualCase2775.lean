/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2775 : Family 10 := level10.get ⟨1011,by decide⟩
def sourceMap2775 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2775 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2775_checked : acceptsGraphIso
    (source (graph core2775) (root 10) 0 4) DegreeTwoThreeSpectrum6002.graph sourceMap2775=true := by decide +kernel
theorem fusedMap2775_checked : acceptsGraphIso
    (fused (graph core2775) (root 10) 0 4) DegreeTwoThreeSpectrum6003.graph fusedMap2775=true := by decide +kernel
theorem certified2775 : Certified (graph core2775) (root 10) 0 4 :=
  of_native_maps core2775 DegreeTwoThreeSpectrum6002.graph DegreeTwoThreeSpectrum6003.graph
    sourceMap2775 fusedMap2775 sourceMap2775_checked fusedMap2775_checked
    DegreeTwoThreeFiniteComparisons.comparison2775
#print axioms sourceMap2775_checked
#print axioms fusedMap2775_checked
#print axioms certified2775
def sourceMap2775swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2775swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2775swap_checked : acceptsGraphIso
    (source (graph core2775) (root 10) 4 0) DegreeTwoThreeSpectrum6002.graph sourceMap2775swap=true := by decide +kernel
theorem fusedMap2775swap_checked : acceptsGraphIso
    (fused (graph core2775) (root 10) 4 0) DegreeTwoThreeSpectrum6003.graph fusedMap2775swap=true := by decide +kernel
theorem certified2775swap : Certified (graph core2775) (root 10) 4 0 :=
  of_native_maps core2775 DegreeTwoThreeSpectrum6002.graph DegreeTwoThreeSpectrum6003.graph
    sourceMap2775swap fusedMap2775swap sourceMap2775swap_checked fusedMap2775swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2775
#print axioms sourceMap2775swap_checked
#print axioms fusedMap2775swap_checked
#print axioms certified2775swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
