/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core064 : Family 7 := level7.get ⟨80,by decide⟩
def sourceMap064 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap064 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![4,0,1,2,3,7,8,9,5,6] (fusedLabel 7 0 0 v)
theorem sourceMap064_checked : acceptsGraphIso
    (source (graph core064) (root 7) 0 0) SmallGeFourSpectrum028.graph
      sourceMap064=true := by decide +kernel
theorem fusedMap064_checked : acceptsGraphIso
    (fused (graph core064) (root 7) 0 0) SmallGeFourSpectrum018.graph
      fusedMap064=true := by decide +kernel
theorem certified064 : Certified (graph core064) (root 7) 0 0 :=
  of_native_maps core064 SmallGeFourSpectrum028.graph SmallGeFourSpectrum018.graph
    sourceMap064 fusedMap064 sourceMap064_checked fusedMap064_checked
    SmallGeFourComparisons.comparison064
#print axioms sourceMap064_checked
#print axioms fusedMap064_checked
#print axioms certified064
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
