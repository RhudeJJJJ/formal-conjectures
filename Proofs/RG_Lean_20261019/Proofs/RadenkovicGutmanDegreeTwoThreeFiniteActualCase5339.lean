/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5339 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap5339 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5339 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5339_checked : acceptsGraphIso
    (source (graph core5339) (root 6) 3 4) DegreeTwoThreeSpectrum4607.graph sourceMap5339=true := by decide +kernel
theorem fusedMap5339_checked : acceptsGraphIso
    (fused (graph core5339) (root 6) 3 4) DegreeTwoThreeSpectrum3872.graph fusedMap5339=true := by decide +kernel
theorem certified5339 : Certified (graph core5339) (root 6) 3 4 :=
  of_native_maps core5339 DegreeTwoThreeSpectrum4607.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap5339 fusedMap5339 sourceMap5339_checked fusedMap5339_checked
    DegreeTwoThreeFiniteComparisons.comparison5339
#print axioms sourceMap5339_checked
#print axioms fusedMap5339_checked
#print axioms certified5339
def sourceMap5339swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,15,6,7,8,9] (sourceLabel 6 4 3 v)
def fusedMap5339swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5339swap_checked : acceptsGraphIso
    (source (graph core5339) (root 6) 4 3) DegreeTwoThreeSpectrum4607.graph sourceMap5339swap=true := by decide +kernel
theorem fusedMap5339swap_checked : acceptsGraphIso
    (fused (graph core5339) (root 6) 4 3) DegreeTwoThreeSpectrum3872.graph fusedMap5339swap=true := by decide +kernel
theorem certified5339swap : Certified (graph core5339) (root 6) 4 3 :=
  of_native_maps core5339 DegreeTwoThreeSpectrum4607.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap5339swap fusedMap5339swap sourceMap5339swap_checked fusedMap5339swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5339
#print axioms sourceMap5339swap_checked
#print axioms fusedMap5339swap_checked
#print axioms certified5339swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
