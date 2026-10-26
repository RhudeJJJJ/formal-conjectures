/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3868 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap3868 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3868 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3868_checked : acceptsGraphIso
    (source (graph core3868) (root 8) 1 4) DegreeTwoThreeSpectrum4434.graph sourceMap3868=true := by decide +kernel
theorem fusedMap3868_checked : acceptsGraphIso
    (fused (graph core3868) (root 8) 1 4) DegreeTwoThreeSpectrum3992.graph fusedMap3868=true := by decide +kernel
theorem certified3868 : Certified (graph core3868) (root 8) 1 4 :=
  of_native_maps core3868 DegreeTwoThreeSpectrum4434.graph DegreeTwoThreeSpectrum3992.graph
    sourceMap3868 fusedMap3868 sourceMap3868_checked fusedMap3868_checked
    DegreeTwoThreeFiniteComparisons.comparison3868
#print axioms sourceMap3868_checked
#print axioms fusedMap3868_checked
#print axioms certified3868
def sourceMap3868swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3868swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3868swap_checked : acceptsGraphIso
    (source (graph core3868) (root 8) 4 1) DegreeTwoThreeSpectrum4434.graph sourceMap3868swap=true := by decide +kernel
theorem fusedMap3868swap_checked : acceptsGraphIso
    (fused (graph core3868) (root 8) 4 1) DegreeTwoThreeSpectrum3992.graph fusedMap3868swap=true := by decide +kernel
theorem certified3868swap : Certified (graph core3868) (root 8) 4 1 :=
  of_native_maps core3868 DegreeTwoThreeSpectrum4434.graph DegreeTwoThreeSpectrum3992.graph
    sourceMap3868swap fusedMap3868swap sourceMap3868swap_checked fusedMap3868swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3868
#print axioms sourceMap3868swap_checked
#print axioms fusedMap3868swap_checked
#print axioms certified3868swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
