/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5233 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap5233 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,6,7,8,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5233 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5233_checked : acceptsGraphIso
    (source (graph core5233) (root 6) 2 5) DegreeTwoThreeSpectrum4335.graph sourceMap5233=true := by decide +kernel
theorem fusedMap5233_checked : acceptsGraphIso
    (fused (graph core5233) (root 6) 2 5) DegreeTwoThreeSpectrum3946.graph fusedMap5233=true := by decide +kernel
theorem certified5233 : Certified (graph core5233) (root 6) 2 5 :=
  of_native_maps core5233 DegreeTwoThreeSpectrum4335.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap5233 fusedMap5233 sourceMap5233_checked fusedMap5233_checked
    DegreeTwoThreeFiniteComparisons.comparison5233
#print axioms sourceMap5233_checked
#print axioms fusedMap5233_checked
#print axioms certified5233
def sourceMap5233swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,0,11,12,13,14,15,6,7,8] (sourceLabel 6 5 2 v)
def fusedMap5233swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5233swap_checked : acceptsGraphIso
    (source (graph core5233) (root 6) 5 2) DegreeTwoThreeSpectrum4335.graph sourceMap5233swap=true := by decide +kernel
theorem fusedMap5233swap_checked : acceptsGraphIso
    (fused (graph core5233) (root 6) 5 2) DegreeTwoThreeSpectrum3946.graph fusedMap5233swap=true := by decide +kernel
theorem certified5233swap : Certified (graph core5233) (root 6) 5 2 :=
  of_native_maps core5233 DegreeTwoThreeSpectrum4335.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap5233swap fusedMap5233swap sourceMap5233swap_checked fusedMap5233swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5233
#print axioms sourceMap5233swap_checked
#print axioms fusedMap5233swap_checked
#print axioms certified5233swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
