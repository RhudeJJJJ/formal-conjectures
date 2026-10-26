/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3734 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3734 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (sourceLabel 5 0 9 v)
def fusedMap3734 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 0 9 v)
theorem sourceMap3734_checked : acceptsGraphIso
    (source (graph core3734) (root 5) 0 9) DegreeTwoThreeSpectrum5050.graph sourceMap3734=true := by decide +kernel
theorem fusedMap3734_checked : acceptsGraphIso
    (fused (graph core3734) (root 5) 0 9) DegreeTwoThreeSpectrum5055.graph fusedMap3734=true := by decide +kernel
theorem certified3734 : Certified (graph core3734) (root 5) 0 9 :=
  of_native_maps core3734 DegreeTwoThreeSpectrum5050.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap3734 fusedMap3734 sourceMap3734_checked fusedMap3734_checked
    DegreeTwoThreeFiniteComparisons.comparison3734
#print axioms sourceMap3734_checked
#print axioms fusedMap3734_checked
#print axioms certified3734
def sourceMap3734swap : (Vertices 5 ⊕ Fin 10 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 5 9 0 v)
def fusedMap3734swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 9 0 v)
theorem sourceMap3734swap_checked : acceptsGraphIso
    (source (graph core3734) (root 5) 9 0) DegreeTwoThreeSpectrum5050.graph sourceMap3734swap=true := by decide +kernel
theorem fusedMap3734swap_checked : acceptsGraphIso
    (fused (graph core3734) (root 5) 9 0) DegreeTwoThreeSpectrum5055.graph fusedMap3734swap=true := by decide +kernel
theorem certified3734swap : Certified (graph core3734) (root 5) 9 0 :=
  of_native_maps core3734 DegreeTwoThreeSpectrum5050.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap3734swap fusedMap3734swap sourceMap3734swap_checked fusedMap3734swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3734
#print axioms sourceMap3734swap_checked
#print axioms fusedMap3734swap_checked
#print axioms certified3734swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
