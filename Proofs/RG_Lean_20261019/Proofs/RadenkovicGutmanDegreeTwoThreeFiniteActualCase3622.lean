/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3622 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap3622 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3622 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3622_checked : acceptsGraphIso
    (source (graph core3622) (root 8) 0 6) DegreeTwoThreeSpectrum6531.graph sourceMap3622=true := by decide +kernel
theorem fusedMap3622_checked : acceptsGraphIso
    (fused (graph core3622) (root 8) 0 6) DegreeTwoThreeSpectrum5441.graph fusedMap3622=true := by decide +kernel
theorem certified3622 : Certified (graph core3622) (root 8) 0 6 :=
  of_native_maps core3622 DegreeTwoThreeSpectrum6531.graph DegreeTwoThreeSpectrum5441.graph
    sourceMap3622 fusedMap3622 sourceMap3622_checked fusedMap3622_checked
    DegreeTwoThreeFiniteComparisons.comparison3622
#print axioms sourceMap3622_checked
#print axioms fusedMap3622_checked
#print axioms certified3622
def sourceMap3622swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3622swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3622swap_checked : acceptsGraphIso
    (source (graph core3622) (root 8) 6 0) DegreeTwoThreeSpectrum6531.graph sourceMap3622swap=true := by decide +kernel
theorem fusedMap3622swap_checked : acceptsGraphIso
    (fused (graph core3622) (root 8) 6 0) DegreeTwoThreeSpectrum5441.graph fusedMap3622swap=true := by decide +kernel
theorem certified3622swap : Certified (graph core3622) (root 8) 6 0 :=
  of_native_maps core3622 DegreeTwoThreeSpectrum6531.graph DegreeTwoThreeSpectrum5441.graph
    sourceMap3622swap fusedMap3622swap sourceMap3622swap_checked fusedMap3622swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3622
#print axioms sourceMap3622swap_checked
#print axioms fusedMap3622swap_checked
#print axioms certified3622swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
