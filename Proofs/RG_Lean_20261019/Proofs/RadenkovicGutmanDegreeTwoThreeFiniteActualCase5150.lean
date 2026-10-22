/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5150 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap5150 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5150 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5150_checked : acceptsGraphIso
    (source (graph core5150) (root 8) 2 4) DegreeTwoThreeSpectrum6270.graph sourceMap5150=true := by decide +kernel
theorem fusedMap5150_checked : acceptsGraphIso
    (fused (graph core5150) (root 8) 2 4) DegreeTwoThreeSpectrum5258.graph fusedMap5150=true := by decide +kernel
theorem certified5150 : Certified (graph core5150) (root 8) 2 4 :=
  of_native_maps core5150 DegreeTwoThreeSpectrum6270.graph DegreeTwoThreeSpectrum5258.graph
    sourceMap5150 fusedMap5150 sourceMap5150_checked fusedMap5150_checked
    DegreeTwoThreeFiniteComparisons.comparison5150
#print axioms sourceMap5150_checked
#print axioms fusedMap5150_checked
#print axioms certified5150
def sourceMap5150swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5150swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5150swap_checked : acceptsGraphIso
    (source (graph core5150) (root 8) 4 2) DegreeTwoThreeSpectrum6270.graph sourceMap5150swap=true := by decide +kernel
theorem fusedMap5150swap_checked : acceptsGraphIso
    (fused (graph core5150) (root 8) 4 2) DegreeTwoThreeSpectrum5258.graph fusedMap5150swap=true := by decide +kernel
theorem certified5150swap : Certified (graph core5150) (root 8) 4 2 :=
  of_native_maps core5150 DegreeTwoThreeSpectrum6270.graph DegreeTwoThreeSpectrum5258.graph
    sourceMap5150swap fusedMap5150swap sourceMap5150swap_checked fusedMap5150swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5150
#print axioms sourceMap5150swap_checked
#print axioms fusedMap5150swap_checked
#print axioms certified5150swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
