/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5262 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap5262 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5262 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5262_checked : acceptsGraphIso
    (source (graph core5262) (root 7) 2 5) DegreeTwoThreeSpectrum6092.graph sourceMap5262=true := by decide +kernel
theorem fusedMap5262_checked : acceptsGraphIso
    (fused (graph core5262) (root 7) 2 5) DegreeTwoThreeSpectrum5173.graph fusedMap5262=true := by decide +kernel
theorem certified5262 : Certified (graph core5262) (root 7) 2 5 :=
  of_native_maps core5262 DegreeTwoThreeSpectrum6092.graph DegreeTwoThreeSpectrum5173.graph
    sourceMap5262 fusedMap5262 sourceMap5262_checked fusedMap5262_checked
    DegreeTwoThreeFiniteComparisons.comparison5262
#print axioms sourceMap5262_checked
#print axioms fusedMap5262_checked
#print axioms certified5262
def sourceMap5262swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5262swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5262swap_checked : acceptsGraphIso
    (source (graph core5262) (root 7) 5 2) DegreeTwoThreeSpectrum6092.graph sourceMap5262swap=true := by decide +kernel
theorem fusedMap5262swap_checked : acceptsGraphIso
    (fused (graph core5262) (root 7) 5 2) DegreeTwoThreeSpectrum5173.graph fusedMap5262swap=true := by decide +kernel
theorem certified5262swap : Certified (graph core5262) (root 7) 5 2 :=
  of_native_maps core5262 DegreeTwoThreeSpectrum6092.graph DegreeTwoThreeSpectrum5173.graph
    sourceMap5262swap fusedMap5262swap sourceMap5262swap_checked fusedMap5262swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5262
#print axioms sourceMap5262swap_checked
#print axioms fusedMap5262swap_checked
#print axioms certified5262swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
