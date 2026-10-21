/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core210 : Family 9 := level9.get ⟨647,by decide⟩
def sourceMap210 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap210 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap210_checked : acceptsGraphIso
    (source (graph core210) (root 9) 0 0) SmallGeFourSpectrum175.graph
      sourceMap210=true := by decide +kernel
theorem fusedMap210_checked : acceptsGraphIso
    (fused (graph core210) (root 9) 0 0) SmallGeFourSpectrum170.graph
      fusedMap210=true := by decide +kernel
theorem certified210 : Certified (graph core210) (root 9) 0 0 :=
  of_native_maps core210 SmallGeFourSpectrum175.graph SmallGeFourSpectrum170.graph
    sourceMap210 fusedMap210 sourceMap210_checked fusedMap210_checked
    SmallGeFourComparisons.comparison210
#print axioms sourceMap210_checked
#print axioms fusedMap210_checked
#print axioms certified210
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
