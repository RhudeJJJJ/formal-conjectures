/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3100 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap3100 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3100 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3100_checked : acceptsGraphIso
    (source (graph core3100) (root 6) 0 5) DegreeTwoThreeSpectrum1936.graph sourceMap3100=true := by decide +kernel
theorem fusedMap3100_checked : acceptsGraphIso
    (fused (graph core3100) (root 6) 0 5) DegreeTwoThreeSpectrum1739.graph fusedMap3100=true := by decide +kernel
theorem certified3100 : Certified (graph core3100) (root 6) 0 5 :=
  of_native_maps core3100 DegreeTwoThreeSpectrum1936.graph DegreeTwoThreeSpectrum1739.graph
    sourceMap3100 fusedMap3100 sourceMap3100_checked fusedMap3100_checked
    DegreeTwoThreeFiniteComparisons.comparison3100
#print axioms sourceMap3100_checked
#print axioms fusedMap3100_checked
#print axioms certified3100
def sourceMap3100swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,9] (sourceLabel 6 5 0 v)
def fusedMap3100swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3100swap_checked : acceptsGraphIso
    (source (graph core3100) (root 6) 5 0) DegreeTwoThreeSpectrum1936.graph sourceMap3100swap=true := by decide +kernel
theorem fusedMap3100swap_checked : acceptsGraphIso
    (fused (graph core3100) (root 6) 5 0) DegreeTwoThreeSpectrum1739.graph fusedMap3100swap=true := by decide +kernel
theorem certified3100swap : Certified (graph core3100) (root 6) 5 0 :=
  of_native_maps core3100 DegreeTwoThreeSpectrum1936.graph DegreeTwoThreeSpectrum1739.graph
    sourceMap3100swap fusedMap3100swap sourceMap3100swap_checked fusedMap3100swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3100
#print axioms sourceMap3100swap_checked
#print axioms fusedMap3100swap_checked
#print axioms certified3100swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
