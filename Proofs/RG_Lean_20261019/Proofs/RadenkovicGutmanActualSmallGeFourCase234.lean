/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core234 : Family 9 := level9.get ⟨705,by decide⟩
def sourceMap234 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap234 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap234_checked : acceptsGraphIso
    (source (graph core234) (root 9) 0 0) SmallGeFourSpectrum221.graph
      sourceMap234=true := by decide +kernel
theorem fusedMap234_checked : acceptsGraphIso
    (fused (graph core234) (root 9) 0 0) SmallGeFourSpectrum220.graph
      fusedMap234=true := by decide +kernel
theorem certified234 : Certified (graph core234) (root 9) 0 0 :=
  of_native_maps core234 SmallGeFourSpectrum221.graph SmallGeFourSpectrum220.graph
    sourceMap234 fusedMap234 sourceMap234_checked fusedMap234_checked
    SmallGeFourComparisons.comparison234
#print axioms sourceMap234_checked
#print axioms fusedMap234_checked
#print axioms certified234
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
