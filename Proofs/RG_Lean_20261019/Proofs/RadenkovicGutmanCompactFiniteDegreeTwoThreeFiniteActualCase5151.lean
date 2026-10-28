/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5151 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap5151 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5151 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5151_checked : acceptsGraphIso
    (source (graph core5151) (root 8) 2 4) DegreeTwoThreeSpectrum6307.graph sourceMap5151=true := by decide +kernel
theorem fusedMap5151_checked : acceptsGraphIso
    (fused (graph core5151) (root 8) 2 4) DegreeTwoThreeSpectrum5276.graph fusedMap5151=true := by decide +kernel
theorem certified5151 : Certified (graph core5151) (root 8) 2 4 :=
  of_native_maps core5151 DegreeTwoThreeSpectrum6307.graph DegreeTwoThreeSpectrum5276.graph
    sourceMap5151 fusedMap5151 sourceMap5151_checked fusedMap5151_checked
    DegreeTwoThreeFiniteComparisons.comparison5151
#print axioms sourceMap5151_checked
#print axioms fusedMap5151_checked
#print axioms certified5151
def sourceMap5151swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5151swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5151swap_checked : acceptsGraphIso
    (source (graph core5151) (root 8) 4 2) DegreeTwoThreeSpectrum6307.graph sourceMap5151swap=true := by decide +kernel
theorem fusedMap5151swap_checked : acceptsGraphIso
    (fused (graph core5151) (root 8) 4 2) DegreeTwoThreeSpectrum5276.graph fusedMap5151swap=true := by decide +kernel
theorem certified5151swap : Certified (graph core5151) (root 8) 4 2 :=
  of_native_maps core5151 DegreeTwoThreeSpectrum6307.graph DegreeTwoThreeSpectrum5276.graph
    sourceMap5151swap fusedMap5151swap sourceMap5151swap_checked fusedMap5151swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5151
#print axioms sourceMap5151swap_checked
#print axioms fusedMap5151swap_checked
#print axioms certified5151swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
