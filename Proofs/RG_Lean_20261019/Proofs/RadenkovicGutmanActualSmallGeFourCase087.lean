/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core087 : Family 7 := level7.get ⟨109,by decide⟩
def sourceMap087 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (sourceLabel 7 1 1 v)
def fusedMap087 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap087_checked : acceptsGraphIso
    (source (graph core087) (root 7) 1 1) SmallGeFourSpectrum226.graph
      sourceMap087=true := by decide +kernel
theorem fusedMap087_checked : acceptsGraphIso
    (fused (graph core087) (root 7) 1 1) SmallGeFourSpectrum144.graph
      fusedMap087=true := by decide +kernel
theorem certified087 : Certified (graph core087) (root 7) 1 1 :=
  of_native_maps core087 SmallGeFourSpectrum226.graph SmallGeFourSpectrum144.graph
    sourceMap087 fusedMap087 sourceMap087_checked fusedMap087_checked
    SmallGeFourComparisons.comparison087
#print axioms sourceMap087_checked
#print axioms fusedMap087_checked
#print axioms certified087
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
