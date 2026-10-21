/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core131 : Family 8 := level8.get ⟨247,by decide⟩
def sourceMap131 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,3,4,5,6,1,2] (sourceLabel 8 0 1 v)
def fusedMap131 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 0 1 v)
theorem sourceMap131_checked : acceptsGraphIso
    (source (graph core131) (root 8) 0 1) SmallGeFourSpectrum181.graph
      sourceMap131=true := by decide +kernel
theorem fusedMap131_checked : acceptsGraphIso
    (fused (graph core131) (root 8) 0 1) SmallGeFourSpectrum189.graph
      fusedMap131=true := by decide +kernel
theorem certified131 : Certified (graph core131) (root 8) 0 1 :=
  of_native_maps core131 SmallGeFourSpectrum181.graph SmallGeFourSpectrum189.graph
    sourceMap131 fusedMap131 sourceMap131_checked fusedMap131_checked
    SmallGeFourComparisons.comparison131
#print axioms sourceMap131_checked
#print axioms fusedMap131_checked
#print axioms certified131
def sourceMap131swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,3,4,5,1,2,6] (sourceLabel 8 1 0 v)
def fusedMap131swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 1 0 v)
theorem sourceMap131swap_checked : acceptsGraphIso
    (source (graph core131) (root 8) 1 0) SmallGeFourSpectrum181.graph
      sourceMap131swap=true := by decide +kernel
theorem fusedMap131swap_checked : acceptsGraphIso
    (fused (graph core131) (root 8) 1 0) SmallGeFourSpectrum189.graph
      fusedMap131swap=true := by decide +kernel
theorem certified131swap : Certified (graph core131) (root 8) 1 0 :=
  of_native_maps core131 SmallGeFourSpectrum181.graph SmallGeFourSpectrum189.graph
    sourceMap131swap fusedMap131swap sourceMap131swap_checked fusedMap131swap_checked
    SmallGeFourComparisons.comparison131
#print axioms sourceMap131swap_checked
#print axioms fusedMap131swap_checked
#print axioms certified131swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
