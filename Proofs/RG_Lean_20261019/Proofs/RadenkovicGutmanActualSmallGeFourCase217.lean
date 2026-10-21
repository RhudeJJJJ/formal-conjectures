/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core217 : Family 9 := level9.get ⟨671,by decide⟩
def sourceMap217 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap217 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,7,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap217_checked : acceptsGraphIso
    (source (graph core217) (root 9) 0 0) SmallGeFourSpectrum168.graph
      sourceMap217=true := by decide +kernel
theorem fusedMap217_checked : acceptsGraphIso
    (fused (graph core217) (root 9) 0 0) SmallGeFourSpectrum165.graph
      fusedMap217=true := by decide +kernel
theorem certified217 : Certified (graph core217) (root 9) 0 0 :=
  of_native_maps core217 SmallGeFourSpectrum168.graph SmallGeFourSpectrum165.graph
    sourceMap217 fusedMap217 sourceMap217_checked fusedMap217_checked
    SmallGeFourComparisons.comparison217
#print axioms sourceMap217_checked
#print axioms fusedMap217_checked
#print axioms certified217
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
