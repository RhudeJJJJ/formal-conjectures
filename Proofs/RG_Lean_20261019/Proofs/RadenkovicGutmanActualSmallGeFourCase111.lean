/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core111 : Family 8 := level8.get ⟨131,by decide⟩
def sourceMap111 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 8 0 1 v)
def fusedMap111 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (fusedLabel 8 0 1 v)
theorem sourceMap111_checked : acceptsGraphIso
    (source (graph core111) (root 8) 0 1) SmallGeFourSpectrum159.graph
      sourceMap111=true := by decide +kernel
theorem fusedMap111_checked : acceptsGraphIso
    (fused (graph core111) (root 8) 0 1) SmallGeFourSpectrum098.graph
      fusedMap111=true := by decide +kernel
theorem certified111 : Certified (graph core111) (root 8) 0 1 :=
  of_native_maps core111 SmallGeFourSpectrum159.graph SmallGeFourSpectrum098.graph
    sourceMap111 fusedMap111 sourceMap111_checked fusedMap111_checked
    SmallGeFourComparisons.comparison111
#print axioms sourceMap111_checked
#print axioms fusedMap111_checked
#print axioms certified111
def sourceMap111swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7,11] (sourceLabel 8 1 0 v)
def fusedMap111swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (fusedLabel 8 1 0 v)
theorem sourceMap111swap_checked : acceptsGraphIso
    (source (graph core111) (root 8) 1 0) SmallGeFourSpectrum159.graph
      sourceMap111swap=true := by decide +kernel
theorem fusedMap111swap_checked : acceptsGraphIso
    (fused (graph core111) (root 8) 1 0) SmallGeFourSpectrum098.graph
      fusedMap111swap=true := by decide +kernel
theorem certified111swap : Certified (graph core111) (root 8) 1 0 :=
  of_native_maps core111 SmallGeFourSpectrum159.graph SmallGeFourSpectrum098.graph
    sourceMap111swap fusedMap111swap sourceMap111swap_checked fusedMap111swap_checked
    SmallGeFourComparisons.comparison111
#print axioms sourceMap111swap_checked
#print axioms fusedMap111swap_checked
#print axioms certified111swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
