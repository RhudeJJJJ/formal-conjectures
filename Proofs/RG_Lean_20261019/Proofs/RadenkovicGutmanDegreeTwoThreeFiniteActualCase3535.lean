/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3535 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap3535 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3535 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3535_checked : acceptsGraphIso
    (source (graph core3535) (root 7) 0 6) DegreeTwoThreeSpectrum4566.graph sourceMap3535=true := by decide +kernel
theorem fusedMap3535_checked : acceptsGraphIso
    (fused (graph core3535) (root 7) 0 6) DegreeTwoThreeSpectrum4063.graph fusedMap3535=true := by decide +kernel
theorem certified3535 : Certified (graph core3535) (root 7) 0 6 :=
  of_native_maps core3535 DegreeTwoThreeSpectrum4566.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap3535 fusedMap3535 sourceMap3535_checked fusedMap3535_checked
    DegreeTwoThreeFiniteComparisons.comparison3535
#print axioms sourceMap3535_checked
#print axioms fusedMap3535_checked
#print axioms certified3535
def sourceMap3535swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3535swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3535swap_checked : acceptsGraphIso
    (source (graph core3535) (root 7) 6 0) DegreeTwoThreeSpectrum4566.graph sourceMap3535swap=true := by decide +kernel
theorem fusedMap3535swap_checked : acceptsGraphIso
    (fused (graph core3535) (root 7) 6 0) DegreeTwoThreeSpectrum4063.graph fusedMap3535swap=true := by decide +kernel
theorem certified3535swap : Certified (graph core3535) (root 7) 6 0 :=
  of_native_maps core3535 DegreeTwoThreeSpectrum4566.graph DegreeTwoThreeSpectrum4063.graph
    sourceMap3535swap fusedMap3535swap sourceMap3535swap_checked fusedMap3535swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3535
#print axioms sourceMap3535swap_checked
#print axioms fusedMap3535swap_checked
#print axioms certified3535swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
