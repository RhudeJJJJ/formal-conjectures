/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2026 : Family 10 := level10.get ⟨1703,by decide⟩
def sourceMap2026 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap2026 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2026_checked : acceptsGraphIso
    (source (graph core2026) (root 10) 0 2) DegreeTwoThreeSpectrum3820.graph sourceMap2026=true := by decide +kernel
theorem fusedMap2026_checked : acceptsGraphIso
    (fused (graph core2026) (root 10) 0 2) DegreeTwoThreeSpectrum3378.graph fusedMap2026=true := by decide +kernel
theorem certified2026 : Certified (graph core2026) (root 10) 0 2 :=
  of_native_maps core2026 DegreeTwoThreeSpectrum3820.graph DegreeTwoThreeSpectrum3378.graph
    sourceMap2026 fusedMap2026 sourceMap2026_checked fusedMap2026_checked
    DegreeTwoThreeFiniteComparisons.comparison2026
#print axioms sourceMap2026_checked
#print axioms fusedMap2026_checked
#print axioms certified2026
def sourceMap2026swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap2026swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2026swap_checked : acceptsGraphIso
    (source (graph core2026) (root 10) 2 0) DegreeTwoThreeSpectrum3820.graph sourceMap2026swap=true := by decide +kernel
theorem fusedMap2026swap_checked : acceptsGraphIso
    (fused (graph core2026) (root 10) 2 0) DegreeTwoThreeSpectrum3378.graph fusedMap2026swap=true := by decide +kernel
theorem certified2026swap : Certified (graph core2026) (root 10) 2 0 :=
  of_native_maps core2026 DegreeTwoThreeSpectrum3820.graph DegreeTwoThreeSpectrum3378.graph
    sourceMap2026swap fusedMap2026swap sourceMap2026swap_checked fusedMap2026swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2026
#print axioms sourceMap2026swap_checked
#print axioms fusedMap2026swap_checked
#print axioms certified2026swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
