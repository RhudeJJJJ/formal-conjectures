/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5270 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap5270 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5270 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5270_checked : acceptsGraphIso
    (source (graph core5270) (root 7) 2 5) DegreeTwoThreeSpectrum6530.graph sourceMap5270=true := by decide +kernel
theorem fusedMap5270_checked : acceptsGraphIso
    (fused (graph core5270) (root 7) 2 5) DegreeTwoThreeSpectrum5446.graph fusedMap5270=true := by decide +kernel
theorem certified5270 : Certified (graph core5270) (root 7) 2 5 :=
  of_native_maps core5270 DegreeTwoThreeSpectrum6530.graph DegreeTwoThreeSpectrum5446.graph
    sourceMap5270 fusedMap5270 sourceMap5270_checked fusedMap5270_checked
    DegreeTwoThreeFiniteComparisons.comparison5270
#print axioms sourceMap5270_checked
#print axioms fusedMap5270_checked
#print axioms certified5270
def sourceMap5270swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5270swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5270swap_checked : acceptsGraphIso
    (source (graph core5270) (root 7) 5 2) DegreeTwoThreeSpectrum6530.graph sourceMap5270swap=true := by decide +kernel
theorem fusedMap5270swap_checked : acceptsGraphIso
    (fused (graph core5270) (root 7) 5 2) DegreeTwoThreeSpectrum5446.graph fusedMap5270swap=true := by decide +kernel
theorem certified5270swap : Certified (graph core5270) (root 7) 5 2 :=
  of_native_maps core5270 DegreeTwoThreeSpectrum6530.graph DegreeTwoThreeSpectrum5446.graph
    sourceMap5270swap fusedMap5270swap sourceMap5270swap_checked fusedMap5270swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5270
#print axioms sourceMap5270swap_checked
#print axioms fusedMap5270swap_checked
#print axioms certified5270swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
