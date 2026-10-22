/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5164 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap5164 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5164 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5164_checked : acceptsGraphIso
    (source (graph core5164) (root 8) 2 4) DegreeTwoThreeSpectrum6705.graph sourceMap5164=true := by decide +kernel
theorem fusedMap5164_checked : acceptsGraphIso
    (fused (graph core5164) (root 8) 2 4) DegreeTwoThreeSpectrum5556.graph fusedMap5164=true := by decide +kernel
theorem certified5164 : Certified (graph core5164) (root 8) 2 4 :=
  of_native_maps core5164 DegreeTwoThreeSpectrum6705.graph DegreeTwoThreeSpectrum5556.graph
    sourceMap5164 fusedMap5164 sourceMap5164_checked fusedMap5164_checked
    DegreeTwoThreeFiniteComparisons.comparison5164
#print axioms sourceMap5164_checked
#print axioms fusedMap5164_checked
#print axioms certified5164
def sourceMap5164swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5164swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5164swap_checked : acceptsGraphIso
    (source (graph core5164) (root 8) 4 2) DegreeTwoThreeSpectrum6705.graph sourceMap5164swap=true := by decide +kernel
theorem fusedMap5164swap_checked : acceptsGraphIso
    (fused (graph core5164) (root 8) 4 2) DegreeTwoThreeSpectrum5556.graph fusedMap5164swap=true := by decide +kernel
theorem certified5164swap : Certified (graph core5164) (root 8) 4 2 :=
  of_native_maps core5164 DegreeTwoThreeSpectrum6705.graph DegreeTwoThreeSpectrum5556.graph
    sourceMap5164swap fusedMap5164swap sourceMap5164swap_checked fusedMap5164swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5164
#print axioms sourceMap5164swap_checked
#print axioms fusedMap5164swap_checked
#print axioms certified5164swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
