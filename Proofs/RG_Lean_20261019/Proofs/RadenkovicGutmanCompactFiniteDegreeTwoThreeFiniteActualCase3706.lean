/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3706 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3706 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (sourceLabel 5 0 8 v)
def fusedMap3706 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 0 8 v)
theorem sourceMap3706_checked : acceptsGraphIso
    (source (graph core3706) (root 5) 0 8) DegreeTwoThreeSpectrum4026.graph sourceMap3706=true := by decide +kernel
theorem fusedMap3706_checked : acceptsGraphIso
    (fused (graph core3706) (root 5) 0 8) DegreeTwoThreeSpectrum3864.graph fusedMap3706=true := by decide +kernel
theorem certified3706 : Certified (graph core3706) (root 5) 0 8 :=
  of_native_maps core3706 DegreeTwoThreeSpectrum4026.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap3706 fusedMap3706 sourceMap3706_checked fusedMap3706_checked
    DegreeTwoThreeFiniteComparisons.comparison3706
#print axioms sourceMap3706_checked
#print axioms fusedMap3706_checked
#print axioms certified3706
def sourceMap3706swap : (Vertices 5 ⊕ Fin 9 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,9] (sourceLabel 5 8 0 v)
def fusedMap3706swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 8 0 v)
theorem sourceMap3706swap_checked : acceptsGraphIso
    (source (graph core3706) (root 5) 8 0) DegreeTwoThreeSpectrum4026.graph sourceMap3706swap=true := by decide +kernel
theorem fusedMap3706swap_checked : acceptsGraphIso
    (fused (graph core3706) (root 5) 8 0) DegreeTwoThreeSpectrum3864.graph fusedMap3706swap=true := by decide +kernel
theorem certified3706swap : Certified (graph core3706) (root 5) 8 0 :=
  of_native_maps core3706 DegreeTwoThreeSpectrum4026.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap3706swap fusedMap3706swap sourceMap3706swap_checked fusedMap3706swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3706
#print axioms sourceMap3706swap_checked
#print axioms fusedMap3706swap_checked
#print axioms certified3706swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
