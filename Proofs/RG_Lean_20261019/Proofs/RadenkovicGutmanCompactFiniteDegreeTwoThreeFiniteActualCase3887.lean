/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3887 : Family 8 := level8.get ⟨181,by decide⟩
def sourceMap3887 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3887 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3887_checked : acceptsGraphIso
    (source (graph core3887) (root 8) 1 4) DegreeTwoThreeSpectrum4638.graph sourceMap3887=true := by decide +kernel
theorem fusedMap3887_checked : acceptsGraphIso
    (fused (graph core3887) (root 8) 1 4) DegreeTwoThreeSpectrum4117.graph fusedMap3887=true := by decide +kernel
theorem certified3887 : Certified (graph core3887) (root 8) 1 4 :=
  of_native_maps core3887 DegreeTwoThreeSpectrum4638.graph DegreeTwoThreeSpectrum4117.graph
    sourceMap3887 fusedMap3887 sourceMap3887_checked fusedMap3887_checked
    DegreeTwoThreeFiniteComparisons.comparison3887
#print axioms sourceMap3887_checked
#print axioms fusedMap3887_checked
#print axioms certified3887
def sourceMap3887swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3887swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3887swap_checked : acceptsGraphIso
    (source (graph core3887) (root 8) 4 1) DegreeTwoThreeSpectrum4638.graph sourceMap3887swap=true := by decide +kernel
theorem fusedMap3887swap_checked : acceptsGraphIso
    (fused (graph core3887) (root 8) 4 1) DegreeTwoThreeSpectrum4117.graph fusedMap3887swap=true := by decide +kernel
theorem certified3887swap : Certified (graph core3887) (root 8) 4 1 :=
  of_native_maps core3887 DegreeTwoThreeSpectrum4638.graph DegreeTwoThreeSpectrum4117.graph
    sourceMap3887swap fusedMap3887swap sourceMap3887swap_checked fusedMap3887swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3887
#print axioms sourceMap3887swap_checked
#print axioms fusedMap3887swap_checked
#print axioms certified3887swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
