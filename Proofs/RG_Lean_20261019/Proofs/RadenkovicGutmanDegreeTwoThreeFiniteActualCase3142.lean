/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3142 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap3142 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 8 0 5 v)
def fusedMap3142 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3142_checked : acceptsGraphIso
    (source (graph core3142) (root 8) 0 5) DegreeTwoThreeSpectrum4058.graph sourceMap3142=true := by decide +kernel
theorem fusedMap3142_checked : acceptsGraphIso
    (fused (graph core3142) (root 8) 0 5) DegreeTwoThreeSpectrum3867.graph fusedMap3142=true := by decide +kernel
theorem certified3142 : Certified (graph core3142) (root 8) 0 5 :=
  of_native_maps core3142 DegreeTwoThreeSpectrum4058.graph DegreeTwoThreeSpectrum3867.graph
    sourceMap3142 fusedMap3142 sourceMap3142_checked fusedMap3142_checked
    DegreeTwoThreeFiniteComparisons.comparison3142
#print axioms sourceMap3142_checked
#print axioms fusedMap3142_checked
#print axioms certified3142
def sourceMap3142swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13,15] (sourceLabel 8 5 0 v)
def fusedMap3142swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3142swap_checked : acceptsGraphIso
    (source (graph core3142) (root 8) 5 0) DegreeTwoThreeSpectrum4058.graph sourceMap3142swap=true := by decide +kernel
theorem fusedMap3142swap_checked : acceptsGraphIso
    (fused (graph core3142) (root 8) 5 0) DegreeTwoThreeSpectrum3867.graph fusedMap3142swap=true := by decide +kernel
theorem certified3142swap : Certified (graph core3142) (root 8) 5 0 :=
  of_native_maps core3142 DegreeTwoThreeSpectrum4058.graph DegreeTwoThreeSpectrum3867.graph
    sourceMap3142swap fusedMap3142swap sourceMap3142swap_checked fusedMap3142swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3142
#print axioms sourceMap3142swap_checked
#print axioms fusedMap3142swap_checked
#print axioms certified3142swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
