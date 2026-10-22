/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5271 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap5271 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5271 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5271_checked : acceptsGraphIso
    (source (graph core5271) (root 7) 2 5) DegreeTwoThreeSpectrum6598.graph sourceMap5271=true := by decide +kernel
theorem fusedMap5271_checked : acceptsGraphIso
    (fused (graph core5271) (root 7) 2 5) DegreeTwoThreeSpectrum5489.graph fusedMap5271=true := by decide +kernel
theorem certified5271 : Certified (graph core5271) (root 7) 2 5 :=
  of_native_maps core5271 DegreeTwoThreeSpectrum6598.graph DegreeTwoThreeSpectrum5489.graph
    sourceMap5271 fusedMap5271 sourceMap5271_checked fusedMap5271_checked
    DegreeTwoThreeFiniteComparisons.comparison5271
#print axioms sourceMap5271_checked
#print axioms fusedMap5271_checked
#print axioms certified5271
def sourceMap5271swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5271swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5271swap_checked : acceptsGraphIso
    (source (graph core5271) (root 7) 5 2) DegreeTwoThreeSpectrum6598.graph sourceMap5271swap=true := by decide +kernel
theorem fusedMap5271swap_checked : acceptsGraphIso
    (fused (graph core5271) (root 7) 5 2) DegreeTwoThreeSpectrum5489.graph fusedMap5271swap=true := by decide +kernel
theorem certified5271swap : Certified (graph core5271) (root 7) 5 2 :=
  of_native_maps core5271 DegreeTwoThreeSpectrum6598.graph DegreeTwoThreeSpectrum5489.graph
    sourceMap5271swap fusedMap5271swap sourceMap5271swap_checked fusedMap5271swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5271
#print axioms sourceMap5271swap_checked
#print axioms fusedMap5271swap_checked
#print axioms certified5271swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
