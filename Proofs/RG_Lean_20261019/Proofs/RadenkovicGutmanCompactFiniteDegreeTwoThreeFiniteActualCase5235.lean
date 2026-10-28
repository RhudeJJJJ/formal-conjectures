/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5235 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap5235 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5235 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5235_checked : acceptsGraphIso
    (source (graph core5235) (root 6) 2 5) DegreeTwoThreeSpectrum4457.graph sourceMap5235=true := by decide +kernel
theorem fusedMap5235_checked : acceptsGraphIso
    (fused (graph core5235) (root 6) 2 5) DegreeTwoThreeSpectrum4008.graph fusedMap5235=true := by decide +kernel
theorem certified5235 : Certified (graph core5235) (root 6) 2 5 :=
  of_native_maps core5235 DegreeTwoThreeSpectrum4457.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap5235 fusedMap5235 sourceMap5235_checked fusedMap5235_checked
    DegreeTwoThreeFiniteComparisons.comparison5235
#print axioms sourceMap5235_checked
#print axioms fusedMap5235_checked
#print axioms certified5235
def sourceMap5235swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,7,8,9] (sourceLabel 6 5 2 v)
def fusedMap5235swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5235swap_checked : acceptsGraphIso
    (source (graph core5235) (root 6) 5 2) DegreeTwoThreeSpectrum4457.graph sourceMap5235swap=true := by decide +kernel
theorem fusedMap5235swap_checked : acceptsGraphIso
    (fused (graph core5235) (root 6) 5 2) DegreeTwoThreeSpectrum4008.graph fusedMap5235swap=true := by decide +kernel
theorem certified5235swap : Certified (graph core5235) (root 6) 5 2 :=
  of_native_maps core5235 DegreeTwoThreeSpectrum4457.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap5235swap fusedMap5235swap sourceMap5235swap_checked fusedMap5235swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5235
#print axioms sourceMap5235swap_checked
#print axioms fusedMap5235swap_checked
#print axioms certified5235swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
