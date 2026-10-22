/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5358 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5358 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,2,3,4,5,0,11,12,13,14,15] (sourceLabel 5 3 5 v)
def fusedMap5358 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 3 5 v)
theorem sourceMap5358_checked : acceptsGraphIso
    (source (graph core5358) (root 5) 3 5) DegreeTwoThreeSpectrum4633.graph sourceMap5358=true := by decide +kernel
theorem fusedMap5358_checked : acceptsGraphIso
    (fused (graph core5358) (root 5) 3 5) DegreeTwoThreeSpectrum3856.graph fusedMap5358=true := by decide +kernel
theorem certified5358 : Certified (graph core5358) (root 5) 3 5 :=
  of_native_maps core5358 DegreeTwoThreeSpectrum4633.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap5358 fusedMap5358 sourceMap5358_checked fusedMap5358_checked
    DegreeTwoThreeFiniteComparisons.comparison5358
#print axioms sourceMap5358_checked
#print axioms fusedMap5358_checked
#print axioms certified5358
def sourceMap5358swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,0,11,12,13,14,15,2,3,4,5] (sourceLabel 5 5 3 v)
def fusedMap5358swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 5 3 v)
theorem sourceMap5358swap_checked : acceptsGraphIso
    (source (graph core5358) (root 5) 5 3) DegreeTwoThreeSpectrum4633.graph sourceMap5358swap=true := by decide +kernel
theorem fusedMap5358swap_checked : acceptsGraphIso
    (fused (graph core5358) (root 5) 5 3) DegreeTwoThreeSpectrum3856.graph fusedMap5358swap=true := by decide +kernel
theorem certified5358swap : Certified (graph core5358) (root 5) 5 3 :=
  of_native_maps core5358 DegreeTwoThreeSpectrum4633.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap5358swap fusedMap5358swap sourceMap5358swap_checked fusedMap5358swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5358
#print axioms sourceMap5358swap_checked
#print axioms fusedMap5358swap_checked
#print axioms certified5358swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
