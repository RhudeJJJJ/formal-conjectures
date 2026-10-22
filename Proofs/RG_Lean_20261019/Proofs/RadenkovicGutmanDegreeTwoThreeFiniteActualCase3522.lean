/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3522 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap3522 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3522 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3522_checked : acceptsGraphIso
    (source (graph core3522) (root 7) 0 6) DegreeTwoThreeSpectrum4226.graph sourceMap3522=true := by decide +kernel
theorem fusedMap3522_checked : acceptsGraphIso
    (fused (graph core3522) (root 7) 0 6) DegreeTwoThreeSpectrum3899.graph fusedMap3522=true := by decide +kernel
theorem certified3522 : Certified (graph core3522) (root 7) 0 6 :=
  of_native_maps core3522 DegreeTwoThreeSpectrum4226.graph DegreeTwoThreeSpectrum3899.graph
    sourceMap3522 fusedMap3522 sourceMap3522_checked fusedMap3522_checked
    DegreeTwoThreeFiniteComparisons.comparison3522
#print axioms sourceMap3522_checked
#print axioms fusedMap3522_checked
#print axioms certified3522
def sourceMap3522swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3522swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3522swap_checked : acceptsGraphIso
    (source (graph core3522) (root 7) 6 0) DegreeTwoThreeSpectrum4226.graph sourceMap3522swap=true := by decide +kernel
theorem fusedMap3522swap_checked : acceptsGraphIso
    (fused (graph core3522) (root 7) 6 0) DegreeTwoThreeSpectrum3899.graph fusedMap3522swap=true := by decide +kernel
theorem certified3522swap : Certified (graph core3522) (root 7) 6 0 :=
  of_native_maps core3522 DegreeTwoThreeSpectrum4226.graph DegreeTwoThreeSpectrum3899.graph
    sourceMap3522swap fusedMap3522swap sourceMap3522swap_checked fusedMap3522swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3522
#print axioms sourceMap3522swap_checked
#print axioms fusedMap3522swap_checked
#print axioms certified3522swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
