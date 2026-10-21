/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core136 : Family 8 := level8.get ⟨256,by decide⟩
def sourceMap136 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap136 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap136_checked : acceptsGraphIso
    (source (graph core136) (root 8) 0 0) SmallGeFourSpectrum068.graph
      sourceMap136=true := by decide +kernel
theorem fusedMap136_checked : acceptsGraphIso
    (fused (graph core136) (root 8) 0 0) SmallGeFourSpectrum067.graph
      fusedMap136=true := by decide +kernel
theorem certified136 : Certified (graph core136) (root 8) 0 0 :=
  of_native_maps core136 SmallGeFourSpectrum068.graph SmallGeFourSpectrum067.graph
    sourceMap136 fusedMap136 sourceMap136_checked fusedMap136_checked
    SmallGeFourComparisons.comparison136
#print axioms sourceMap136_checked
#print axioms fusedMap136_checked
#print axioms certified136
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
