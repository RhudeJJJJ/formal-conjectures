/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3234 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap3234 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3234 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3234_checked : acceptsGraphIso
    (source (graph core3234) (root 8) 0 5) DegreeTwoThreeSpectrum4680.graph sourceMap3234=true := by decide +kernel
theorem fusedMap3234_checked : acceptsGraphIso
    (fused (graph core3234) (root 8) 0 5) DegreeTwoThreeSpectrum4182.graph fusedMap3234=true := by decide +kernel
theorem certified3234 : Certified (graph core3234) (root 8) 0 5 :=
  of_native_maps core3234 DegreeTwoThreeSpectrum4680.graph DegreeTwoThreeSpectrum4182.graph
    sourceMap3234 fusedMap3234 sourceMap3234_checked fusedMap3234_checked
    DegreeTwoThreeFiniteComparisons.comparison3234
#print axioms sourceMap3234_checked
#print axioms fusedMap3234_checked
#print axioms certified3234
def sourceMap3234swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,11] (sourceLabel 8 5 0 v)
def fusedMap3234swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3234swap_checked : acceptsGraphIso
    (source (graph core3234) (root 8) 5 0) DegreeTwoThreeSpectrum4680.graph sourceMap3234swap=true := by decide +kernel
theorem fusedMap3234swap_checked : acceptsGraphIso
    (fused (graph core3234) (root 8) 5 0) DegreeTwoThreeSpectrum4182.graph fusedMap3234swap=true := by decide +kernel
theorem certified3234swap : Certified (graph core3234) (root 8) 5 0 :=
  of_native_maps core3234 DegreeTwoThreeSpectrum4680.graph DegreeTwoThreeSpectrum4182.graph
    sourceMap3234swap fusedMap3234swap sourceMap3234swap_checked fusedMap3234swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3234
#print axioms sourceMap3234swap_checked
#print axioms fusedMap3234swap_checked
#print axioms certified3234swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
