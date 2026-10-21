/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core224 : Family 9 := level9.get ⟨684,by decide⟩
def sourceMap224 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap224 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,6,7,8,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap224_checked : acceptsGraphIso
    (source (graph core224) (root 9) 0 0) SmallGeFourSpectrum146.graph
      sourceMap224=true := by decide +kernel
theorem fusedMap224_checked : acceptsGraphIso
    (fused (graph core224) (root 9) 0 0) SmallGeFourSpectrum141.graph
      fusedMap224=true := by decide +kernel
theorem certified224 : Certified (graph core224) (root 9) 0 0 :=
  of_native_maps core224 SmallGeFourSpectrum146.graph SmallGeFourSpectrum141.graph
    sourceMap224 fusedMap224 sourceMap224_checked fusedMap224_checked
    SmallGeFourComparisons.comparison224
#print axioms sourceMap224_checked
#print axioms fusedMap224_checked
#print axioms certified224
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
