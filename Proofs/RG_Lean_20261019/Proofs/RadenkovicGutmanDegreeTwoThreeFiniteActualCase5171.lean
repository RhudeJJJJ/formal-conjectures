/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5171 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap5171 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5171 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5171_checked : acceptsGraphIso
    (source (graph core5171) (root 8) 2 4) DegreeTwoThreeSpectrum6908.graph sourceMap5171=true := by decide +kernel
theorem fusedMap5171_checked : acceptsGraphIso
    (fused (graph core5171) (root 8) 2 4) DegreeTwoThreeSpectrum5697.graph fusedMap5171=true := by decide +kernel
theorem certified5171 : Certified (graph core5171) (root 8) 2 4 :=
  of_native_maps core5171 DegreeTwoThreeSpectrum6908.graph DegreeTwoThreeSpectrum5697.graph
    sourceMap5171 fusedMap5171 sourceMap5171_checked fusedMap5171_checked
    DegreeTwoThreeFiniteComparisons.comparison5171
#print axioms sourceMap5171_checked
#print axioms fusedMap5171_checked
#print axioms certified5171
def sourceMap5171swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5171swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5171swap_checked : acceptsGraphIso
    (source (graph core5171) (root 8) 4 2) DegreeTwoThreeSpectrum6908.graph sourceMap5171swap=true := by decide +kernel
theorem fusedMap5171swap_checked : acceptsGraphIso
    (fused (graph core5171) (root 8) 4 2) DegreeTwoThreeSpectrum5697.graph fusedMap5171swap=true := by decide +kernel
theorem certified5171swap : Certified (graph core5171) (root 8) 4 2 :=
  of_native_maps core5171 DegreeTwoThreeSpectrum6908.graph DegreeTwoThreeSpectrum5697.graph
    sourceMap5171swap fusedMap5171swap sourceMap5171swap_checked fusedMap5171swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5171
#print axioms sourceMap5171swap_checked
#print axioms fusedMap5171swap_checked
#print axioms certified5171swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
