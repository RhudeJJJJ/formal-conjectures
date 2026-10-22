/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5336 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap5336 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,15,11,12,13,14,6,7,8,9,10] (sourceLabel 6 3 4 v)
def fusedMap5336 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5336_checked : acceptsGraphIso
    (source (graph core5336) (root 6) 3 4) DegreeTwoThreeSpectrum4658.graph sourceMap5336=true := by decide +kernel
theorem fusedMap5336_checked : acceptsGraphIso
    (fused (graph core5336) (root 6) 3 4) DegreeTwoThreeSpectrum3887.graph fusedMap5336=true := by decide +kernel
theorem certified5336 : Certified (graph core5336) (root 6) 3 4 :=
  of_native_maps core5336 DegreeTwoThreeSpectrum4658.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap5336 fusedMap5336 sourceMap5336_checked fusedMap5336_checked
    DegreeTwoThreeFiniteComparisons.comparison5336
#print axioms sourceMap5336_checked
#print axioms fusedMap5336_checked
#print axioms certified5336
def sourceMap5336swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,15,6,7,8,9,10,11,12,13,14] (sourceLabel 6 4 3 v)
def fusedMap5336swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5336swap_checked : acceptsGraphIso
    (source (graph core5336) (root 6) 4 3) DegreeTwoThreeSpectrum4658.graph sourceMap5336swap=true := by decide +kernel
theorem fusedMap5336swap_checked : acceptsGraphIso
    (fused (graph core5336) (root 6) 4 3) DegreeTwoThreeSpectrum3887.graph fusedMap5336swap=true := by decide +kernel
theorem certified5336swap : Certified (graph core5336) (root 6) 4 3 :=
  of_native_maps core5336 DegreeTwoThreeSpectrum4658.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap5336swap fusedMap5336swap sourceMap5336swap_checked fusedMap5336swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5336
#print axioms sourceMap5336swap_checked
#print axioms fusedMap5336swap_checked
#print axioms certified5336swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
