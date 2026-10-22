/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3890 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap3890 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3890 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3890_checked : acceptsGraphIso
    (source (graph core3890) (root 8) 1 4) DegreeTwoThreeSpectrum4684.graph sourceMap3890=true := by decide +kernel
theorem fusedMap3890_checked : acceptsGraphIso
    (fused (graph core3890) (root 8) 1 4) DegreeTwoThreeSpectrum4190.graph fusedMap3890=true := by decide +kernel
theorem certified3890 : Certified (graph core3890) (root 8) 1 4 :=
  of_native_maps core3890 DegreeTwoThreeSpectrum4684.graph DegreeTwoThreeSpectrum4190.graph
    sourceMap3890 fusedMap3890 sourceMap3890_checked fusedMap3890_checked
    DegreeTwoThreeFiniteComparisons.comparison3890
#print axioms sourceMap3890_checked
#print axioms fusedMap3890_checked
#print axioms certified3890
def sourceMap3890swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3890swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3890swap_checked : acceptsGraphIso
    (source (graph core3890) (root 8) 4 1) DegreeTwoThreeSpectrum4684.graph sourceMap3890swap=true := by decide +kernel
theorem fusedMap3890swap_checked : acceptsGraphIso
    (fused (graph core3890) (root 8) 4 1) DegreeTwoThreeSpectrum4190.graph fusedMap3890swap=true := by decide +kernel
theorem certified3890swap : Certified (graph core3890) (root 8) 4 1 :=
  of_native_maps core3890 DegreeTwoThreeSpectrum4684.graph DegreeTwoThreeSpectrum4190.graph
    sourceMap3890swap fusedMap3890swap sourceMap3890swap_checked fusedMap3890swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3890
#print axioms sourceMap3890swap_checked
#print axioms fusedMap3890swap_checked
#print axioms certified3890swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
