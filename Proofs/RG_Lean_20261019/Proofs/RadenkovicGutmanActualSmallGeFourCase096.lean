/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core096 : Family 7 := level7.get ⟨112,by decide⟩
def sourceMap096 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap096 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6] (fusedLabel 7 0 0 v)
theorem sourceMap096_checked : acceptsGraphIso
    (source (graph core096) (root 7) 0 0) SmallGeFourSpectrum035.graph
      sourceMap096=true := by decide +kernel
theorem fusedMap096_checked : acceptsGraphIso
    (fused (graph core096) (root 7) 0 0) SmallGeFourSpectrum034.graph
      fusedMap096=true := by decide +kernel
theorem certified096 : Certified (graph core096) (root 7) 0 0 :=
  of_native_maps core096 SmallGeFourSpectrum035.graph SmallGeFourSpectrum034.graph
    sourceMap096 fusedMap096 sourceMap096_checked fusedMap096_checked
    SmallGeFourComparisons.comparison096
#print axioms sourceMap096_checked
#print axioms fusedMap096_checked
#print axioms certified096
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
