/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5274 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap5274 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,6,7,8,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5274 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5274_checked : acceptsGraphIso
    (source (graph core5274) (root 7) 2 5) DegreeTwoThreeSpectrum6677.graph sourceMap5274=true := by decide +kernel
theorem fusedMap5274_checked : acceptsGraphIso
    (fused (graph core5274) (root 7) 2 5) DegreeTwoThreeSpectrum5549.graph fusedMap5274=true := by decide +kernel
theorem certified5274 : Certified (graph core5274) (root 7) 2 5 :=
  of_native_maps core5274 DegreeTwoThreeSpectrum6677.graph DegreeTwoThreeSpectrum5549.graph
    sourceMap5274 fusedMap5274 sourceMap5274_checked fusedMap5274_checked
    DegreeTwoThreeFiniteComparisons.comparison5274
#print axioms sourceMap5274_checked
#print axioms fusedMap5274_checked
#print axioms certified5274
def sourceMap5274swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,0,12,13,14,15,16,6,7,8] (sourceLabel 7 5 2 v)
def fusedMap5274swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5274swap_checked : acceptsGraphIso
    (source (graph core5274) (root 7) 5 2) DegreeTwoThreeSpectrum6677.graph sourceMap5274swap=true := by decide +kernel
theorem fusedMap5274swap_checked : acceptsGraphIso
    (fused (graph core5274) (root 7) 5 2) DegreeTwoThreeSpectrum5549.graph fusedMap5274swap=true := by decide +kernel
theorem certified5274swap : Certified (graph core5274) (root 7) 5 2 :=
  of_native_maps core5274 DegreeTwoThreeSpectrum6677.graph DegreeTwoThreeSpectrum5549.graph
    sourceMap5274swap fusedMap5274swap sourceMap5274swap_checked fusedMap5274swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5274
#print axioms sourceMap5274swap_checked
#print axioms fusedMap5274swap_checked
#print axioms certified5274swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
