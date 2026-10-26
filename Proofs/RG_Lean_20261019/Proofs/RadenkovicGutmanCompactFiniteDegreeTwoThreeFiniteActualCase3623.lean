/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3623 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap3623 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3623 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3623_checked : acceptsGraphIso
    (source (graph core3623) (root 8) 0 6) DegreeTwoThreeSpectrum6537.graph sourceMap3623=true := by decide +kernel
theorem fusedMap3623_checked : acceptsGraphIso
    (fused (graph core3623) (root 8) 0 6) DegreeTwoThreeSpectrum5442.graph fusedMap3623=true := by decide +kernel
theorem certified3623 : Certified (graph core3623) (root 8) 0 6 :=
  of_native_maps core3623 DegreeTwoThreeSpectrum6537.graph DegreeTwoThreeSpectrum5442.graph
    sourceMap3623 fusedMap3623 sourceMap3623_checked fusedMap3623_checked
    DegreeTwoThreeFiniteComparisons.comparison3623
#print axioms sourceMap3623_checked
#print axioms fusedMap3623_checked
#print axioms certified3623
def sourceMap3623swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3623swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3623swap_checked : acceptsGraphIso
    (source (graph core3623) (root 8) 6 0) DegreeTwoThreeSpectrum6537.graph sourceMap3623swap=true := by decide +kernel
theorem fusedMap3623swap_checked : acceptsGraphIso
    (fused (graph core3623) (root 8) 6 0) DegreeTwoThreeSpectrum5442.graph fusedMap3623swap=true := by decide +kernel
theorem certified3623swap : Certified (graph core3623) (root 8) 6 0 :=
  of_native_maps core3623 DegreeTwoThreeSpectrum6537.graph DegreeTwoThreeSpectrum5442.graph
    sourceMap3623swap fusedMap3623swap sourceMap3623swap_checked fusedMap3623swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3623
#print axioms sourceMap3623swap_checked
#print axioms fusedMap3623swap_checked
#print axioms certified3623swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
