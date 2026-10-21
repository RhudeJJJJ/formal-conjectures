/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core085 : Family 7 := level7.get ⟨109,by decide⟩
def sourceMap085 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,8,9,10,6,7] (sourceLabel 7 0 1 v)
def fusedMap085 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap085_checked : acceptsGraphIso
    (source (graph core085) (root 7) 0 1) SmallGeFourSpectrum086.graph
      sourceMap085=true := by decide +kernel
theorem fusedMap085_checked : acceptsGraphIso
    (fused (graph core085) (root 7) 0 1) SmallGeFourSpectrum047.graph
      fusedMap085=true := by decide +kernel
theorem certified085 : Certified (graph core085) (root 7) 0 1 :=
  of_native_maps core085 SmallGeFourSpectrum086.graph SmallGeFourSpectrum047.graph
    sourceMap085 fusedMap085 sourceMap085_checked fusedMap085_checked
    SmallGeFourComparisons.comparison085
#print axioms sourceMap085_checked
#print axioms fusedMap085_checked
#print axioms certified085
def sourceMap085swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,8,9,6,7,10] (sourceLabel 7 1 0 v)
def fusedMap085swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap085swap_checked : acceptsGraphIso
    (source (graph core085) (root 7) 1 0) SmallGeFourSpectrum086.graph
      sourceMap085swap=true := by decide +kernel
theorem fusedMap085swap_checked : acceptsGraphIso
    (fused (graph core085) (root 7) 1 0) SmallGeFourSpectrum047.graph
      fusedMap085swap=true := by decide +kernel
theorem certified085swap : Certified (graph core085) (root 7) 1 0 :=
  of_native_maps core085 SmallGeFourSpectrum086.graph SmallGeFourSpectrum047.graph
    sourceMap085swap fusedMap085swap sourceMap085swap_checked fusedMap085swap_checked
    SmallGeFourComparisons.comparison085
#print axioms sourceMap085swap_checked
#print axioms fusedMap085swap_checked
#print axioms certified085swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
