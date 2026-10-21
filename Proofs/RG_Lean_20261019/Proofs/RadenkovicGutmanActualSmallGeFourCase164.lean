/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core164 : Family 8 := level8.get ⟨283,by decide⟩
def sourceMap164 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap164 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap164_checked : acceptsGraphIso
    (source (graph core164) (root 8) 0 0) SmallGeFourSpectrum091.graph
      sourceMap164=true := by decide +kernel
theorem fusedMap164_checked : acceptsGraphIso
    (fused (graph core164) (root 8) 0 0) SmallGeFourSpectrum090.graph
      fusedMap164=true := by decide +kernel
theorem certified164 : Certified (graph core164) (root 8) 0 0 :=
  of_native_maps core164 SmallGeFourSpectrum091.graph SmallGeFourSpectrum090.graph
    sourceMap164 fusedMap164 sourceMap164_checked fusedMap164_checked
    SmallGeFourComparisons.comparison164
#print axioms sourceMap164_checked
#print axioms fusedMap164_checked
#print axioms certified164
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
