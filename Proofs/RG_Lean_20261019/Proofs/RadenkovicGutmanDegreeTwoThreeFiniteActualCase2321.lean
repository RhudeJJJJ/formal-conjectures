/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2321 : Family 9 := level9.get ⟨350,by decide⟩
def sourceMap2321 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2321 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2321_checked : acceptsGraphIso
    (source (graph core2321) (root 9) 0 4) DegreeTwoThreeSpectrum4250.graph sourceMap2321=true := by decide +kernel
theorem fusedMap2321_checked : acceptsGraphIso
    (fused (graph core2321) (root 9) 0 4) DegreeTwoThreeSpectrum4251.graph fusedMap2321=true := by decide +kernel
theorem certified2321 : Certified (graph core2321) (root 9) 0 4 :=
  of_native_maps core2321 DegreeTwoThreeSpectrum4250.graph DegreeTwoThreeSpectrum4251.graph
    sourceMap2321 fusedMap2321 sourceMap2321_checked fusedMap2321_checked
    DegreeTwoThreeFiniteComparisons.comparison2321
#print axioms sourceMap2321_checked
#print axioms fusedMap2321_checked
#print axioms certified2321
def sourceMap2321swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2321swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2321swap_checked : acceptsGraphIso
    (source (graph core2321) (root 9) 4 0) DegreeTwoThreeSpectrum4250.graph sourceMap2321swap=true := by decide +kernel
theorem fusedMap2321swap_checked : acceptsGraphIso
    (fused (graph core2321) (root 9) 4 0) DegreeTwoThreeSpectrum4251.graph fusedMap2321swap=true := by decide +kernel
theorem certified2321swap : Certified (graph core2321) (root 9) 4 0 :=
  of_native_maps core2321 DegreeTwoThreeSpectrum4250.graph DegreeTwoThreeSpectrum4251.graph
    sourceMap2321swap fusedMap2321swap sourceMap2321swap_checked fusedMap2321swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2321
#print axioms sourceMap2321swap_checked
#print axioms fusedMap2321swap_checked
#print axioms certified2321swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
