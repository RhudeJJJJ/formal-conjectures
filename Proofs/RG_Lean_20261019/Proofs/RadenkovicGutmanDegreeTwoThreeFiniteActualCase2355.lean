/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2355 : Family 9 := level9.get ⟨435,by decide⟩
def sourceMap2355 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2355 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2355_checked : acceptsGraphIso
    (source (graph core2355) (root 9) 0 4) DegreeTwoThreeSpectrum4432.graph sourceMap2355=true := by decide +kernel
theorem fusedMap2355_checked : acceptsGraphIso
    (fused (graph core2355) (root 9) 0 4) DegreeTwoThreeSpectrum4433.graph fusedMap2355=true := by decide +kernel
theorem certified2355 : Certified (graph core2355) (root 9) 0 4 :=
  of_native_maps core2355 DegreeTwoThreeSpectrum4432.graph DegreeTwoThreeSpectrum4433.graph
    sourceMap2355 fusedMap2355 sourceMap2355_checked fusedMap2355_checked
    DegreeTwoThreeFiniteComparisons.comparison2355
#print axioms sourceMap2355_checked
#print axioms fusedMap2355_checked
#print axioms certified2355
def sourceMap2355swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2355swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2355swap_checked : acceptsGraphIso
    (source (graph core2355) (root 9) 4 0) DegreeTwoThreeSpectrum4432.graph sourceMap2355swap=true := by decide +kernel
theorem fusedMap2355swap_checked : acceptsGraphIso
    (fused (graph core2355) (root 9) 4 0) DegreeTwoThreeSpectrum4433.graph fusedMap2355swap=true := by decide +kernel
theorem certified2355swap : Certified (graph core2355) (root 9) 4 0 :=
  of_native_maps core2355 DegreeTwoThreeSpectrum4432.graph DegreeTwoThreeSpectrum4433.graph
    sourceMap2355swap fusedMap2355swap sourceMap2355swap_checked fusedMap2355swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2355
#print axioms sourceMap2355swap_checked
#print axioms fusedMap2355swap_checked
#print axioms certified2355swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
