/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5153 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap5153 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5153 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5153_checked : acceptsGraphIso
    (source (graph core5153) (root 8) 2 4) DegreeTwoThreeSpectrum6376.graph sourceMap5153=true := by decide +kernel
theorem fusedMap5153_checked : acceptsGraphIso
    (fused (graph core5153) (root 8) 2 4) DegreeTwoThreeSpectrum5322.graph fusedMap5153=true := by decide +kernel
theorem certified5153 : Certified (graph core5153) (root 8) 2 4 :=
  of_native_maps core5153 DegreeTwoThreeSpectrum6376.graph DegreeTwoThreeSpectrum5322.graph
    sourceMap5153 fusedMap5153 sourceMap5153_checked fusedMap5153_checked
    DegreeTwoThreeFiniteComparisons.comparison5153
#print axioms sourceMap5153_checked
#print axioms fusedMap5153_checked
#print axioms certified5153
def sourceMap5153swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5153swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5153swap_checked : acceptsGraphIso
    (source (graph core5153) (root 8) 4 2) DegreeTwoThreeSpectrum6376.graph sourceMap5153swap=true := by decide +kernel
theorem fusedMap5153swap_checked : acceptsGraphIso
    (fused (graph core5153) (root 8) 4 2) DegreeTwoThreeSpectrum5322.graph fusedMap5153swap=true := by decide +kernel
theorem certified5153swap : Certified (graph core5153) (root 8) 4 2 :=
  of_native_maps core5153 DegreeTwoThreeSpectrum6376.graph DegreeTwoThreeSpectrum5322.graph
    sourceMap5153swap fusedMap5153swap sourceMap5153swap_checked fusedMap5153swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5153
#print axioms sourceMap5153swap_checked
#print axioms fusedMap5153swap_checked
#print axioms certified5153swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
