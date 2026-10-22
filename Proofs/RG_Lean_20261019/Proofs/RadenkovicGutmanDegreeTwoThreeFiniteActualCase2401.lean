/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2401 : Family 9 := level9.get ⟨548,by decide⟩
def sourceMap2401 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2401 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2401_checked : acceptsGraphIso
    (source (graph core2401) (root 9) 0 4) DegreeTwoThreeSpectrum4675.graph sourceMap2401=true := by decide +kernel
theorem fusedMap2401_checked : acceptsGraphIso
    (fused (graph core2401) (root 9) 0 4) DegreeTwoThreeSpectrum4177.graph fusedMap2401=true := by decide +kernel
theorem certified2401 : Certified (graph core2401) (root 9) 0 4 :=
  of_native_maps core2401 DegreeTwoThreeSpectrum4675.graph DegreeTwoThreeSpectrum4177.graph
    sourceMap2401 fusedMap2401 sourceMap2401_checked fusedMap2401_checked
    DegreeTwoThreeFiniteComparisons.comparison2401
#print axioms sourceMap2401_checked
#print axioms fusedMap2401_checked
#print axioms certified2401
def sourceMap2401swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2401swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2401swap_checked : acceptsGraphIso
    (source (graph core2401) (root 9) 4 0) DegreeTwoThreeSpectrum4675.graph sourceMap2401swap=true := by decide +kernel
theorem fusedMap2401swap_checked : acceptsGraphIso
    (fused (graph core2401) (root 9) 4 0) DegreeTwoThreeSpectrum4177.graph fusedMap2401swap=true := by decide +kernel
theorem certified2401swap : Certified (graph core2401) (root 9) 4 0 :=
  of_native_maps core2401 DegreeTwoThreeSpectrum4675.graph DegreeTwoThreeSpectrum4177.graph
    sourceMap2401swap fusedMap2401swap sourceMap2401swap_checked fusedMap2401swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2401
#print axioms sourceMap2401swap_checked
#print axioms fusedMap2401swap_checked
#print axioms certified2401swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
