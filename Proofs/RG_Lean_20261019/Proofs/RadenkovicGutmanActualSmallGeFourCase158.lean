/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core158 : Family 8 := level8.get ⟨280,by decide⟩
def sourceMap158 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap158 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,6,7,8,9,10,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap158_checked : acceptsGraphIso
    (source (graph core158) (root 8) 0 0) SmallGeFourSpectrum070.graph
      sourceMap158=true := by decide +kernel
theorem fusedMap158_checked : acceptsGraphIso
    (fused (graph core158) (root 8) 0 0) SmallGeFourSpectrum087.graph
      fusedMap158=true := by decide +kernel
theorem certified158 : Certified (graph core158) (root 8) 0 0 :=
  of_native_maps core158 SmallGeFourSpectrum070.graph SmallGeFourSpectrum087.graph
    sourceMap158 fusedMap158 sourceMap158_checked fusedMap158_checked
    SmallGeFourComparisons.comparison158
#print axioms sourceMap158_checked
#print axioms fusedMap158_checked
#print axioms certified158
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
