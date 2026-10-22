/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2522 : Family 10 := level10.get ⟨281,by decide⟩
def sourceMap2522 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2522 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2522_checked : acceptsGraphIso
    (source (graph core2522) (root 10) 0 4) DegreeTwoThreeSpectrum5415.graph sourceMap2522=true := by decide +kernel
theorem fusedMap2522_checked : acceptsGraphIso
    (fused (graph core2522) (root 10) 0 4) DegreeTwoThreeSpectrum5419.graph fusedMap2522=true := by decide +kernel
theorem certified2522 : Certified (graph core2522) (root 10) 0 4 :=
  of_native_maps core2522 DegreeTwoThreeSpectrum5415.graph DegreeTwoThreeSpectrum5419.graph
    sourceMap2522 fusedMap2522 sourceMap2522_checked fusedMap2522_checked
    DegreeTwoThreeFiniteComparisons.comparison2522
#print axioms sourceMap2522_checked
#print axioms fusedMap2522_checked
#print axioms certified2522
def sourceMap2522swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2522swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2522swap_checked : acceptsGraphIso
    (source (graph core2522) (root 10) 4 0) DegreeTwoThreeSpectrum5415.graph sourceMap2522swap=true := by decide +kernel
theorem fusedMap2522swap_checked : acceptsGraphIso
    (fused (graph core2522) (root 10) 4 0) DegreeTwoThreeSpectrum5419.graph fusedMap2522swap=true := by decide +kernel
theorem certified2522swap : Certified (graph core2522) (root 10) 4 0 :=
  of_native_maps core2522 DegreeTwoThreeSpectrum5415.graph DegreeTwoThreeSpectrum5419.graph
    sourceMap2522swap fusedMap2522swap sourceMap2522swap_checked fusedMap2522swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2522
#print axioms sourceMap2522swap_checked
#print axioms fusedMap2522swap_checked
#print axioms certified2522swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
