/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core063 : Family 7 := level7.get ⟨61,by decide⟩
def sourceMap063 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,6,7,8,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap063 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 1 1 v)
theorem sourceMap063_checked : acceptsGraphIso
    (source (graph core063) (root 7) 1 1) SmallGeFourSpectrum169.graph
      sourceMap063=true := by decide +kernel
theorem fusedMap063_checked : acceptsGraphIso
    (fused (graph core063) (root 7) 1 1) SmallGeFourSpectrum111.graph
      fusedMap063=true := by decide +kernel
theorem certified063 : Certified (graph core063) (root 7) 1 1 :=
  of_native_maps core063 SmallGeFourSpectrum169.graph SmallGeFourSpectrum111.graph
    sourceMap063 fusedMap063 sourceMap063_checked fusedMap063_checked
    SmallGeFourComparisons.comparison063
#print axioms sourceMap063_checked
#print axioms fusedMap063_checked
#print axioms certified063
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
