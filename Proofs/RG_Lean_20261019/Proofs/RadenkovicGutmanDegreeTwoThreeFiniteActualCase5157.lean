/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5157 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap5157 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5157 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5157_checked : acceptsGraphIso
    (source (graph core5157) (root 8) 2 4) DegreeTwoThreeSpectrum6436.graph sourceMap5157=true := by decide +kernel
theorem fusedMap5157_checked : acceptsGraphIso
    (fused (graph core5157) (root 8) 2 4) DegreeTwoThreeSpectrum5371.graph fusedMap5157=true := by decide +kernel
theorem certified5157 : Certified (graph core5157) (root 8) 2 4 :=
  of_native_maps core5157 DegreeTwoThreeSpectrum6436.graph DegreeTwoThreeSpectrum5371.graph
    sourceMap5157 fusedMap5157 sourceMap5157_checked fusedMap5157_checked
    DegreeTwoThreeFiniteComparisons.comparison5157
#print axioms sourceMap5157_checked
#print axioms fusedMap5157_checked
#print axioms certified5157
def sourceMap5157swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,16,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5157swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5157swap_checked : acceptsGraphIso
    (source (graph core5157) (root 8) 4 2) DegreeTwoThreeSpectrum6436.graph sourceMap5157swap=true := by decide +kernel
theorem fusedMap5157swap_checked : acceptsGraphIso
    (fused (graph core5157) (root 8) 4 2) DegreeTwoThreeSpectrum5371.graph fusedMap5157swap=true := by decide +kernel
theorem certified5157swap : Certified (graph core5157) (root 8) 4 2 :=
  of_native_maps core5157 DegreeTwoThreeSpectrum6436.graph DegreeTwoThreeSpectrum5371.graph
    sourceMap5157swap fusedMap5157swap sourceMap5157swap_checked fusedMap5157swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5157
#print axioms sourceMap5157swap_checked
#print axioms fusedMap5157swap_checked
#print axioms certified5157swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
