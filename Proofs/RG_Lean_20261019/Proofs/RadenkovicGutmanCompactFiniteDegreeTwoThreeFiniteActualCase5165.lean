/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5165 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap5165 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5165 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5165_checked : acceptsGraphIso
    (source (graph core5165) (root 8) 2 4) DegreeTwoThreeSpectrum6719.graph sourceMap5165=true := by decide +kernel
theorem fusedMap5165_checked : acceptsGraphIso
    (fused (graph core5165) (root 8) 2 4) DegreeTwoThreeSpectrum5567.graph fusedMap5165=true := by decide +kernel
theorem certified5165 : Certified (graph core5165) (root 8) 2 4 :=
  of_native_maps core5165 DegreeTwoThreeSpectrum6719.graph DegreeTwoThreeSpectrum5567.graph
    sourceMap5165 fusedMap5165 sourceMap5165_checked fusedMap5165_checked
    DegreeTwoThreeFiniteComparisons.comparison5165
#print axioms sourceMap5165_checked
#print axioms fusedMap5165_checked
#print axioms certified5165
def sourceMap5165swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5165swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5165swap_checked : acceptsGraphIso
    (source (graph core5165) (root 8) 4 2) DegreeTwoThreeSpectrum6719.graph sourceMap5165swap=true := by decide +kernel
theorem fusedMap5165swap_checked : acceptsGraphIso
    (fused (graph core5165) (root 8) 4 2) DegreeTwoThreeSpectrum5567.graph fusedMap5165swap=true := by decide +kernel
theorem certified5165swap : Certified (graph core5165) (root 8) 4 2 :=
  of_native_maps core5165 DegreeTwoThreeSpectrum6719.graph DegreeTwoThreeSpectrum5567.graph
    sourceMap5165swap fusedMap5165swap sourceMap5165swap_checked fusedMap5165swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5165
#print axioms sourceMap5165swap_checked
#print axioms fusedMap5165swap_checked
#print axioms certified5165swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
