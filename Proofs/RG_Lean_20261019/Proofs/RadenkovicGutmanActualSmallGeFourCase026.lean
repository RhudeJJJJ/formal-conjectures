/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core026 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap026 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (sourceLabel 5 1 1 v)
def fusedMap026 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap026_checked : acceptsGraphIso
    (source (graph core026) (root 5) 1 1) SmallGeFourSpectrum035.graph
      sourceMap026=true := by decide +kernel
theorem fusedMap026_checked : acceptsGraphIso
    (fused (graph core026) (root 5) 1 1) SmallGeFourSpectrum015.graph
      fusedMap026=true := by decide +kernel
theorem certified026 : Certified (graph core026) (root 5) 1 1 :=
  of_native_maps core026 SmallGeFourSpectrum035.graph SmallGeFourSpectrum015.graph
    sourceMap026 fusedMap026 sourceMap026_checked fusedMap026_checked
    SmallGeFourComparisons.comparison026
#print axioms sourceMap026_checked
#print axioms fusedMap026_checked
#print axioms certified026
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
