/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2139 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap2139 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 8 0 4 v)
def fusedMap2139 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2139_checked : acceptsGraphIso
    (source (graph core2139) (root 8) 0 4) DegreeTwoThreeSpectrum2940.graph sourceMap2139=true := by decide +kernel
theorem fusedMap2139_checked : acceptsGraphIso
    (fused (graph core2139) (root 8) 0 4) DegreeTwoThreeSpectrum2399.graph fusedMap2139=true := by decide +kernel
theorem certified2139 : Certified (graph core2139) (root 8) 0 4 :=
  of_native_maps core2139 DegreeTwoThreeSpectrum2940.graph DegreeTwoThreeSpectrum2399.graph
    sourceMap2139 fusedMap2139 sourceMap2139_checked fusedMap2139_checked
    DegreeTwoThreeFiniteComparisons.comparison2139
#print axioms sourceMap2139_checked
#print axioms fusedMap2139_checked
#print axioms certified2139
def sourceMap2139swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14] (sourceLabel 8 4 0 v)
def fusedMap2139swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2139swap_checked : acceptsGraphIso
    (source (graph core2139) (root 8) 4 0) DegreeTwoThreeSpectrum2940.graph sourceMap2139swap=true := by decide +kernel
theorem fusedMap2139swap_checked : acceptsGraphIso
    (fused (graph core2139) (root 8) 4 0) DegreeTwoThreeSpectrum2399.graph fusedMap2139swap=true := by decide +kernel
theorem certified2139swap : Certified (graph core2139) (root 8) 4 0 :=
  of_native_maps core2139 DegreeTwoThreeSpectrum2940.graph DegreeTwoThreeSpectrum2399.graph
    sourceMap2139swap fusedMap2139swap sourceMap2139swap_checked fusedMap2139swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2139
#print axioms sourceMap2139swap_checked
#print axioms fusedMap2139swap_checked
#print axioms certified2139swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
