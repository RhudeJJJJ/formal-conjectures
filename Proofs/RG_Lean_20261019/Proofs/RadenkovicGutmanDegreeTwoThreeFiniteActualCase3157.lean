/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3157 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap3157 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3157 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3157_checked : acceptsGraphIso
    (source (graph core3157) (root 8) 0 5) DegreeTwoThreeSpectrum4077.graph sourceMap3157=true := by decide +kernel
theorem fusedMap3157_checked : acceptsGraphIso
    (fused (graph core3157) (root 8) 0 5) DegreeTwoThreeSpectrum4078.graph fusedMap3157=true := by decide +kernel
theorem certified3157 : Certified (graph core3157) (root 8) 0 5 :=
  of_native_maps core3157 DegreeTwoThreeSpectrum4077.graph DegreeTwoThreeSpectrum4078.graph
    sourceMap3157 fusedMap3157 sourceMap3157_checked fusedMap3157_checked
    DegreeTwoThreeFiniteComparisons.comparison3157
#print axioms sourceMap3157_checked
#print axioms fusedMap3157_checked
#print axioms certified3157
def sourceMap3157swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3157swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3157swap_checked : acceptsGraphIso
    (source (graph core3157) (root 8) 5 0) DegreeTwoThreeSpectrum4077.graph sourceMap3157swap=true := by decide +kernel
theorem fusedMap3157swap_checked : acceptsGraphIso
    (fused (graph core3157) (root 8) 5 0) DegreeTwoThreeSpectrum4078.graph fusedMap3157swap=true := by decide +kernel
theorem certified3157swap : Certified (graph core3157) (root 8) 5 0 :=
  of_native_maps core3157 DegreeTwoThreeSpectrum4077.graph DegreeTwoThreeSpectrum4078.graph
    sourceMap3157swap fusedMap3157swap sourceMap3157swap_checked fusedMap3157swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3157
#print axioms sourceMap3157swap_checked
#print axioms fusedMap3157swap_checked
#print axioms certified3157swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
