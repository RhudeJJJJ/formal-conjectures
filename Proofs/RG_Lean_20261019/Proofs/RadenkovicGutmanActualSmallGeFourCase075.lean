/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core075 : Family 7 := level7.get ⟨98,by decide⟩
def sourceMap075 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,7,8,3,4,5,6] (sourceLabel 7 1 1 v)
def fusedMap075 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap075_checked : acceptsGraphIso
    (source (graph core075) (root 7) 1 1) SmallGeFourSpectrum164.graph
      sourceMap075=true := by decide +kernel
theorem fusedMap075_checked : acceptsGraphIso
    (fused (graph core075) (root 7) 1 1) SmallGeFourSpectrum107.graph
      fusedMap075=true := by decide +kernel
theorem certified075 : Certified (graph core075) (root 7) 1 1 :=
  of_native_maps core075 SmallGeFourSpectrum164.graph SmallGeFourSpectrum107.graph
    sourceMap075 fusedMap075 sourceMap075_checked fusedMap075_checked
    SmallGeFourComparisons.comparison075
#print axioms sourceMap075_checked
#print axioms fusedMap075_checked
#print axioms certified075
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
