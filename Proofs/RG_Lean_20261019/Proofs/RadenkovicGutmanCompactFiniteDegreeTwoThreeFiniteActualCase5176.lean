/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5176 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap5176 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5176 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5176_checked : acceptsGraphIso
    (source (graph core5176) (root 8) 2 4) DegreeTwoThreeSpectrum6974.graph sourceMap5176=true := by decide +kernel
theorem fusedMap5176_checked : acceptsGraphIso
    (fused (graph core5176) (root 8) 2 4) DegreeTwoThreeSpectrum5769.graph fusedMap5176=true := by decide +kernel
theorem certified5176 : Certified (graph core5176) (root 8) 2 4 :=
  of_native_maps core5176 DegreeTwoThreeSpectrum6974.graph DegreeTwoThreeSpectrum5769.graph
    sourceMap5176 fusedMap5176 sourceMap5176_checked fusedMap5176_checked
    DegreeTwoThreeFiniteComparisons.comparison5176
#print axioms sourceMap5176_checked
#print axioms fusedMap5176_checked
#print axioms certified5176
def sourceMap5176swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,16,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5176swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5176swap_checked : acceptsGraphIso
    (source (graph core5176) (root 8) 4 2) DegreeTwoThreeSpectrum6974.graph sourceMap5176swap=true := by decide +kernel
theorem fusedMap5176swap_checked : acceptsGraphIso
    (fused (graph core5176) (root 8) 4 2) DegreeTwoThreeSpectrum5769.graph fusedMap5176swap=true := by decide +kernel
theorem certified5176swap : Certified (graph core5176) (root 8) 4 2 :=
  of_native_maps core5176 DegreeTwoThreeSpectrum6974.graph DegreeTwoThreeSpectrum5769.graph
    sourceMap5176swap fusedMap5176swap sourceMap5176swap_checked fusedMap5176swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5176
#print axioms sourceMap5176swap_checked
#print axioms fusedMap5176swap_checked
#print axioms certified5176swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
