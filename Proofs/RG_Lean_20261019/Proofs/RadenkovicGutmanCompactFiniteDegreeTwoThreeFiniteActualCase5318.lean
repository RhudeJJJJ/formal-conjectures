/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5318 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5318 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,7,8,9,4,5,6,2,1,0,10,11,12,13,14,15] (sourceLabel 3 2 8 v)
def fusedMap5318 : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 2 8 v)
theorem sourceMap5318_checked : acceptsGraphIso
    (source (graph core5318) (root 3) 2 8) DegreeTwoThreeSpectrum4071.graph sourceMap5318=true := by decide +kernel
theorem fusedMap5318_checked : acceptsGraphIso
    (fused (graph core5318) (root 3) 2 8) DegreeTwoThreeSpectrum3869.graph fusedMap5318=true := by decide +kernel
theorem certified5318 : Certified (graph core5318) (root 3) 2 8 :=
  of_native_maps core5318 DegreeTwoThreeSpectrum4071.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5318 fusedMap5318 sourceMap5318_checked fusedMap5318_checked
    DegreeTwoThreeFiniteComparisons.comparison5318
#print axioms sourceMap5318_checked
#print axioms fusedMap5318_checked
#print axioms certified5318
def sourceMap5318swap : (Vertices 3 ⊕ Fin 9 ⊕ Fin 3) → Fin 16 :=
  fun v => ![3,7,8,9,2,1,0,10,11,12,13,14,15,4,5,6] (sourceLabel 3 8 2 v)
def fusedMap5318swap : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 8 2 v)
theorem sourceMap5318swap_checked : acceptsGraphIso
    (source (graph core5318) (root 3) 8 2) DegreeTwoThreeSpectrum4071.graph sourceMap5318swap=true := by decide +kernel
theorem fusedMap5318swap_checked : acceptsGraphIso
    (fused (graph core5318) (root 3) 8 2) DegreeTwoThreeSpectrum3869.graph fusedMap5318swap=true := by decide +kernel
theorem certified5318swap : Certified (graph core5318) (root 3) 8 2 :=
  of_native_maps core5318 DegreeTwoThreeSpectrum4071.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5318swap fusedMap5318swap sourceMap5318swap_checked fusedMap5318swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5318
#print axioms sourceMap5318swap_checked
#print axioms fusedMap5318swap_checked
#print axioms certified5318swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
