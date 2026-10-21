/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core086 : Family 7 := level7.get ⟨109,by decide⟩
def sourceMap086 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap086 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap086_checked : acceptsGraphIso
    (source (graph core086) (root 7) 0 2) SmallGeFourSpectrum141.graph
      sourceMap086=true := by decide +kernel
theorem fusedMap086_checked : acceptsGraphIso
    (fused (graph core086) (root 7) 0 2) SmallGeFourSpectrum144.graph
      fusedMap086=true := by decide +kernel
theorem certified086 : Certified (graph core086) (root 7) 0 2 :=
  of_native_maps core086 SmallGeFourSpectrum141.graph SmallGeFourSpectrum144.graph
    sourceMap086 fusedMap086 sourceMap086_checked fusedMap086_checked
    SmallGeFourComparisons.comparison086
#print axioms sourceMap086_checked
#print axioms fusedMap086_checked
#print axioms certified086
def sourceMap086swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap086swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap086swap_checked : acceptsGraphIso
    (source (graph core086) (root 7) 2 0) SmallGeFourSpectrum141.graph
      sourceMap086swap=true := by decide +kernel
theorem fusedMap086swap_checked : acceptsGraphIso
    (fused (graph core086) (root 7) 2 0) SmallGeFourSpectrum144.graph
      fusedMap086swap=true := by decide +kernel
theorem certified086swap : Certified (graph core086) (root 7) 2 0 :=
  of_native_maps core086 SmallGeFourSpectrum141.graph SmallGeFourSpectrum144.graph
    sourceMap086swap fusedMap086swap sourceMap086swap_checked fusedMap086swap_checked
    SmallGeFourComparisons.comparison086
#print axioms sourceMap086swap_checked
#print axioms fusedMap086swap_checked
#print axioms certified086swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
