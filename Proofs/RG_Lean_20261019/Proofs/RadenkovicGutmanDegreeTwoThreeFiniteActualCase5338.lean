/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5338 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap5338 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5338 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5338_checked : acceptsGraphIso
    (source (graph core5338) (root 6) 3 4) DegreeTwoThreeSpectrum4516.graph sourceMap5338=true := by decide +kernel
theorem fusedMap5338_checked : acceptsGraphIso
    (fused (graph core5338) (root 6) 3 4) DegreeTwoThreeSpectrum3865.graph fusedMap5338=true := by decide +kernel
theorem certified5338 : Certified (graph core5338) (root 6) 3 4 :=
  of_native_maps core5338 DegreeTwoThreeSpectrum4516.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap5338 fusedMap5338 sourceMap5338_checked fusedMap5338_checked
    DegreeTwoThreeFiniteComparisons.comparison5338
#print axioms sourceMap5338_checked
#print axioms fusedMap5338_checked
#print axioms certified5338
def sourceMap5338swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,15,6,7,8,9] (sourceLabel 6 4 3 v)
def fusedMap5338swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5338swap_checked : acceptsGraphIso
    (source (graph core5338) (root 6) 4 3) DegreeTwoThreeSpectrum4516.graph sourceMap5338swap=true := by decide +kernel
theorem fusedMap5338swap_checked : acceptsGraphIso
    (fused (graph core5338) (root 6) 4 3) DegreeTwoThreeSpectrum3865.graph fusedMap5338swap=true := by decide +kernel
theorem certified5338swap : Certified (graph core5338) (root 6) 4 3 :=
  of_native_maps core5338 DegreeTwoThreeSpectrum4516.graph DegreeTwoThreeSpectrum3865.graph
    sourceMap5338swap fusedMap5338swap sourceMap5338swap_checked fusedMap5338swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5338
#print axioms sourceMap5338swap_checked
#print axioms fusedMap5338swap_checked
#print axioms certified5338swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
