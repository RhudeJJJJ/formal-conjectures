/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5129 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap5129 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5129 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5129_checked : acceptsGraphIso
    (source (graph core5129) (root 8) 2 4) DegreeTwoThreeSpectrum6452.graph sourceMap5129=true := by decide +kernel
theorem fusedMap5129_checked : acceptsGraphIso
    (fused (graph core5129) (root 8) 2 4) DegreeTwoThreeSpectrum4990.graph fusedMap5129=true := by decide +kernel
theorem certified5129 : Certified (graph core5129) (root 8) 2 4 :=
  of_native_maps core5129 DegreeTwoThreeSpectrum6452.graph DegreeTwoThreeSpectrum4990.graph
    sourceMap5129 fusedMap5129 sourceMap5129_checked fusedMap5129_checked
    DegreeTwoThreeFiniteComparisons.comparison5129
#print axioms sourceMap5129_checked
#print axioms fusedMap5129_checked
#print axioms certified5129
def sourceMap5129swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5129swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5129swap_checked : acceptsGraphIso
    (source (graph core5129) (root 8) 4 2) DegreeTwoThreeSpectrum6452.graph sourceMap5129swap=true := by decide +kernel
theorem fusedMap5129swap_checked : acceptsGraphIso
    (fused (graph core5129) (root 8) 4 2) DegreeTwoThreeSpectrum4990.graph fusedMap5129swap=true := by decide +kernel
theorem certified5129swap : Certified (graph core5129) (root 8) 4 2 :=
  of_native_maps core5129 DegreeTwoThreeSpectrum6452.graph DegreeTwoThreeSpectrum4990.graph
    sourceMap5129swap fusedMap5129swap sourceMap5129swap_checked fusedMap5129swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5129
#print axioms sourceMap5129swap_checked
#print axioms fusedMap5129swap_checked
#print axioms certified5129swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
