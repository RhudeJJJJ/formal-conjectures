/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3193 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap3193 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3193 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3193_checked : acceptsGraphIso
    (source (graph core3193) (root 8) 0 5) DegreeTwoThreeSpectrum4590.graph sourceMap3193=true := by decide +kernel
theorem fusedMap3193_checked : acceptsGraphIso
    (fused (graph core3193) (root 8) 0 5) DegreeTwoThreeSpectrum4072.graph fusedMap3193=true := by decide +kernel
theorem certified3193 : Certified (graph core3193) (root 8) 0 5 :=
  of_native_maps core3193 DegreeTwoThreeSpectrum4590.graph DegreeTwoThreeSpectrum4072.graph
    sourceMap3193 fusedMap3193 sourceMap3193_checked fusedMap3193_checked
    DegreeTwoThreeFiniteComparisons.comparison3193
#print axioms sourceMap3193_checked
#print axioms fusedMap3193_checked
#print axioms certified3193
def sourceMap3193swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3193swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3193swap_checked : acceptsGraphIso
    (source (graph core3193) (root 8) 5 0) DegreeTwoThreeSpectrum4590.graph sourceMap3193swap=true := by decide +kernel
theorem fusedMap3193swap_checked : acceptsGraphIso
    (fused (graph core3193) (root 8) 5 0) DegreeTwoThreeSpectrum4072.graph fusedMap3193swap=true := by decide +kernel
theorem certified3193swap : Certified (graph core3193) (root 8) 5 0 :=
  of_native_maps core3193 DegreeTwoThreeSpectrum4590.graph DegreeTwoThreeSpectrum4072.graph
    sourceMap3193swap fusedMap3193swap sourceMap3193swap_checked fusedMap3193swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3193
#print axioms sourceMap3193swap_checked
#print axioms fusedMap3193swap_checked
#print axioms certified3193swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
