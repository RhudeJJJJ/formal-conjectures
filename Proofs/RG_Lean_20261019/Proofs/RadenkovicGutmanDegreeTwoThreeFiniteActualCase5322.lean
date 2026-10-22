/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5322 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5322 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,7,8,4,5,6,2,1,0,9,10,11,12,13,14,15] (sourceLabel 2 2 9 v)
def fusedMap5322 : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 2 9 v)
theorem sourceMap5322_checked : acceptsGraphIso
    (source (graph core5322) (root 2) 2 9) DegreeTwoThreeSpectrum3871.graph sourceMap5322=true := by decide +kernel
theorem fusedMap5322_checked : acceptsGraphIso
    (fused (graph core5322) (root 2) 2 9) DegreeTwoThreeSpectrum3861.graph fusedMap5322=true := by decide +kernel
theorem certified5322 : Certified (graph core5322) (root 2) 2 9 :=
  of_native_maps core5322 DegreeTwoThreeSpectrum3871.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5322 fusedMap5322 sourceMap5322_checked fusedMap5322_checked
    DegreeTwoThreeFiniteComparisons.comparison5322
#print axioms sourceMap5322_checked
#print axioms fusedMap5322_checked
#print axioms certified5322
def sourceMap5322swap : (Vertices 2 ⊕ Fin 10 ⊕ Fin 3) → Fin 16 :=
  fun v => ![3,7,8,2,1,0,9,10,11,12,13,14,15,4,5,6] (sourceLabel 2 9 2 v)
def fusedMap5322swap : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 9 2 v)
theorem sourceMap5322swap_checked : acceptsGraphIso
    (source (graph core5322) (root 2) 9 2) DegreeTwoThreeSpectrum3871.graph sourceMap5322swap=true := by decide +kernel
theorem fusedMap5322swap_checked : acceptsGraphIso
    (fused (graph core5322) (root 2) 9 2) DegreeTwoThreeSpectrum3861.graph fusedMap5322swap=true := by decide +kernel
theorem certified5322swap : Certified (graph core5322) (root 2) 9 2 :=
  of_native_maps core5322 DegreeTwoThreeSpectrum3871.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5322swap fusedMap5322swap sourceMap5322swap_checked fusedMap5322swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5322
#print axioms sourceMap5322swap_checked
#print axioms fusedMap5322swap_checked
#print axioms certified5322swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
