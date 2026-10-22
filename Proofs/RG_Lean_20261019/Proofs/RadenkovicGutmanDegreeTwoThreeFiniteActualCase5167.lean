/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5167 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap5167 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5167 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5167_checked : acceptsGraphIso
    (source (graph core5167) (root 8) 2 4) DegreeTwoThreeSpectrum6762.graph sourceMap5167=true := by decide +kernel
theorem fusedMap5167_checked : acceptsGraphIso
    (fused (graph core5167) (root 8) 2 4) DegreeTwoThreeSpectrum5601.graph fusedMap5167=true := by decide +kernel
theorem certified5167 : Certified (graph core5167) (root 8) 2 4 :=
  of_native_maps core5167 DegreeTwoThreeSpectrum6762.graph DegreeTwoThreeSpectrum5601.graph
    sourceMap5167 fusedMap5167 sourceMap5167_checked fusedMap5167_checked
    DegreeTwoThreeFiniteComparisons.comparison5167
#print axioms sourceMap5167_checked
#print axioms fusedMap5167_checked
#print axioms certified5167
def sourceMap5167swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5167swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5167swap_checked : acceptsGraphIso
    (source (graph core5167) (root 8) 4 2) DegreeTwoThreeSpectrum6762.graph sourceMap5167swap=true := by decide +kernel
theorem fusedMap5167swap_checked : acceptsGraphIso
    (fused (graph core5167) (root 8) 4 2) DegreeTwoThreeSpectrum5601.graph fusedMap5167swap=true := by decide +kernel
theorem certified5167swap : Certified (graph core5167) (root 8) 4 2 :=
  of_native_maps core5167 DegreeTwoThreeSpectrum6762.graph DegreeTwoThreeSpectrum5601.graph
    sourceMap5167swap fusedMap5167swap sourceMap5167swap_checked fusedMap5167swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5167
#print axioms sourceMap5167swap_checked
#print axioms fusedMap5167swap_checked
#print axioms certified5167swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
