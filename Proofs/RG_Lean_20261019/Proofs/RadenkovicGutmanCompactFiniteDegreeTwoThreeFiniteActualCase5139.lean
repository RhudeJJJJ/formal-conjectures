/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5139 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap5139 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,12,13,14,7,8,9,10,11] (sourceLabel 8 2 4 v)
def fusedMap5139 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5139_checked : acceptsGraphIso
    (source (graph core5139) (root 8) 2 4) DegreeTwoThreeSpectrum6991.graph sourceMap5139=true := by decide +kernel
theorem fusedMap5139_checked : acceptsGraphIso
    (fused (graph core5139) (root 8) 2 4) DegreeTwoThreeSpectrum5067.graph fusedMap5139=true := by decide +kernel
theorem certified5139 : Certified (graph core5139) (root 8) 2 4 :=
  of_native_maps core5139 DegreeTwoThreeSpectrum6991.graph DegreeTwoThreeSpectrum5067.graph
    sourceMap5139 fusedMap5139 sourceMap5139_checked fusedMap5139_checked
    DegreeTwoThreeFiniteComparisons.comparison5139
#print axioms sourceMap5139_checked
#print axioms fusedMap5139_checked
#print axioms certified5139
def sourceMap5139swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,7,8,9,10,11,12,13,14] (sourceLabel 8 4 2 v)
def fusedMap5139swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5139swap_checked : acceptsGraphIso
    (source (graph core5139) (root 8) 4 2) DegreeTwoThreeSpectrum6991.graph sourceMap5139swap=true := by decide +kernel
theorem fusedMap5139swap_checked : acceptsGraphIso
    (fused (graph core5139) (root 8) 4 2) DegreeTwoThreeSpectrum5067.graph fusedMap5139swap=true := by decide +kernel
theorem certified5139swap : Certified (graph core5139) (root 8) 4 2 :=
  of_native_maps core5139 DegreeTwoThreeSpectrum6991.graph DegreeTwoThreeSpectrum5067.graph
    sourceMap5139swap fusedMap5139swap sourceMap5139swap_checked fusedMap5139swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5139
#print axioms sourceMap5139swap_checked
#print axioms fusedMap5139swap_checked
#print axioms certified5139swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
