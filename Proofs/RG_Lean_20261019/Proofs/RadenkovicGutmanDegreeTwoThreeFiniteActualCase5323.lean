/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5323 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5323 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,7,8,9,4,5,6,2,1,0,10,11,12,13,14,15,16] (sourceLabel 3 2 9 v)
def fusedMap5323 : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 2 9 v)
theorem sourceMap5323_checked : acceptsGraphIso
    (source (graph core5323) (root 3) 2 9) DegreeTwoThreeSpectrum5050.graph sourceMap5323=true := by decide +kernel
theorem fusedMap5323_checked : acceptsGraphIso
    (fused (graph core5323) (root 3) 2 9) DegreeTwoThreeSpectrum4960.graph fusedMap5323=true := by decide +kernel
theorem certified5323 : Certified (graph core5323) (root 3) 2 9 :=
  of_native_maps core5323 DegreeTwoThreeSpectrum5050.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap5323 fusedMap5323 sourceMap5323_checked fusedMap5323_checked
    DegreeTwoThreeFiniteComparisons.comparison5323
#print axioms sourceMap5323_checked
#print axioms fusedMap5323_checked
#print axioms certified5323
def sourceMap5323swap : (Vertices 3 ⊕ Fin 10 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,7,8,9,2,1,0,10,11,12,13,14,15,16,4,5,6] (sourceLabel 3 9 2 v)
def fusedMap5323swap : (Vertices 3 ⊕ Fin 13) → Fin 17 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 3 9 2 v)
theorem sourceMap5323swap_checked : acceptsGraphIso
    (source (graph core5323) (root 3) 9 2) DegreeTwoThreeSpectrum5050.graph sourceMap5323swap=true := by decide +kernel
theorem fusedMap5323swap_checked : acceptsGraphIso
    (fused (graph core5323) (root 3) 9 2) DegreeTwoThreeSpectrum4960.graph fusedMap5323swap=true := by decide +kernel
theorem certified5323swap : Certified (graph core5323) (root 3) 9 2 :=
  of_native_maps core5323 DegreeTwoThreeSpectrum5050.graph DegreeTwoThreeSpectrum4960.graph
    sourceMap5323swap fusedMap5323swap sourceMap5323swap_checked fusedMap5323swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5323
#print axioms sourceMap5323swap_checked
#print axioms fusedMap5323swap_checked
#print axioms certified5323swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
