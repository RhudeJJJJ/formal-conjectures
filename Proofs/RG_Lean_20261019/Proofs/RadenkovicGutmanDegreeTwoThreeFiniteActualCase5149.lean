/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5149 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap5149 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5149 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5149_checked : acceptsGraphIso
    (source (graph core5149) (root 8) 2 4) DegreeTwoThreeSpectrum6229.graph sourceMap5149=true := by decide +kernel
theorem fusedMap5149_checked : acceptsGraphIso
    (fused (graph core5149) (root 8) 2 4) DegreeTwoThreeSpectrum5241.graph fusedMap5149=true := by decide +kernel
theorem certified5149 : Certified (graph core5149) (root 8) 2 4 :=
  of_native_maps core5149 DegreeTwoThreeSpectrum6229.graph DegreeTwoThreeSpectrum5241.graph
    sourceMap5149 fusedMap5149 sourceMap5149_checked fusedMap5149_checked
    DegreeTwoThreeFiniteComparisons.comparison5149
#print axioms sourceMap5149_checked
#print axioms fusedMap5149_checked
#print axioms certified5149
def sourceMap5149swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5149swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5149swap_checked : acceptsGraphIso
    (source (graph core5149) (root 8) 4 2) DegreeTwoThreeSpectrum6229.graph sourceMap5149swap=true := by decide +kernel
theorem fusedMap5149swap_checked : acceptsGraphIso
    (fused (graph core5149) (root 8) 4 2) DegreeTwoThreeSpectrum5241.graph fusedMap5149swap=true := by decide +kernel
theorem certified5149swap : Certified (graph core5149) (root 8) 4 2 :=
  of_native_maps core5149 DegreeTwoThreeSpectrum6229.graph DegreeTwoThreeSpectrum5241.graph
    sourceMap5149swap fusedMap5149swap sourceMap5149swap_checked fusedMap5149swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5149
#print axioms sourceMap5149swap_checked
#print axioms fusedMap5149swap_checked
#print axioms certified5149swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
