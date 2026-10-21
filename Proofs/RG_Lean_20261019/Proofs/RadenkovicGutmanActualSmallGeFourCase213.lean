/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core213 : Family 9 := level9.get ⟨662,by decide⟩
def sourceMap213 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap213 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap213_checked : acceptsGraphIso
    (source (graph core213) (root 9) 0 0) SmallGeFourSpectrum181.graph
      sourceMap213=true := by decide +kernel
theorem fusedMap213_checked : acceptsGraphIso
    (fused (graph core213) (root 9) 0 0) SmallGeFourSpectrum171.graph
      fusedMap213=true := by decide +kernel
theorem certified213 : Certified (graph core213) (root 9) 0 0 :=
  of_native_maps core213 SmallGeFourSpectrum181.graph SmallGeFourSpectrum171.graph
    sourceMap213 fusedMap213 sourceMap213_checked fusedMap213_checked
    SmallGeFourComparisons.comparison213
#print axioms sourceMap213_checked
#print axioms fusedMap213_checked
#print axioms certified213
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
