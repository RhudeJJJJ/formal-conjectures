/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2365 : Family 9 := level9.get ⟨463,by decide⟩
def sourceMap2365 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2365 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2365_checked : acceptsGraphIso
    (source (graph core2365) (root 9) 0 4) DegreeTwoThreeSpectrum4492.graph sourceMap2365=true := by decide +kernel
theorem fusedMap2365_checked : acceptsGraphIso
    (fused (graph core2365) (root 9) 0 4) DegreeTwoThreeSpectrum4493.graph fusedMap2365=true := by decide +kernel
theorem certified2365 : Certified (graph core2365) (root 9) 0 4 :=
  of_native_maps core2365 DegreeTwoThreeSpectrum4492.graph DegreeTwoThreeSpectrum4493.graph
    sourceMap2365 fusedMap2365 sourceMap2365_checked fusedMap2365_checked
    DegreeTwoThreeFiniteComparisons.comparison2365
#print axioms sourceMap2365_checked
#print axioms fusedMap2365_checked
#print axioms certified2365
def sourceMap2365swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2365swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2365swap_checked : acceptsGraphIso
    (source (graph core2365) (root 9) 4 0) DegreeTwoThreeSpectrum4492.graph sourceMap2365swap=true := by decide +kernel
theorem fusedMap2365swap_checked : acceptsGraphIso
    (fused (graph core2365) (root 9) 4 0) DegreeTwoThreeSpectrum4493.graph fusedMap2365swap=true := by decide +kernel
theorem certified2365swap : Certified (graph core2365) (root 9) 4 0 :=
  of_native_maps core2365 DegreeTwoThreeSpectrum4492.graph DegreeTwoThreeSpectrum4493.graph
    sourceMap2365swap fusedMap2365swap sourceMap2365swap_checked fusedMap2365swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2365
#print axioms sourceMap2365swap_checked
#print axioms fusedMap2365swap_checked
#print axioms certified2365swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
