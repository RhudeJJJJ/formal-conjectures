/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core104 : Family 7 := level7.get ⟨114,by decide⟩
def sourceMap104 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap104 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap104_checked : acceptsGraphIso
    (source (graph core104) (root 7) 0 0) SmallGeFourSpectrum036.graph
      sourceMap104=true := by decide +kernel
theorem fusedMap104_checked : acceptsGraphIso
    (fused (graph core104) (root 7) 0 0) SmallGeFourSpectrum024.graph
      fusedMap104=true := by decide +kernel
theorem certified104 : Certified (graph core104) (root 7) 0 0 :=
  of_native_maps core104 SmallGeFourSpectrum036.graph SmallGeFourSpectrum024.graph
    sourceMap104 fusedMap104 sourceMap104_checked fusedMap104_checked
    SmallGeFourComparisons.comparison104
#print axioms sourceMap104_checked
#print axioms fusedMap104_checked
#print axioms certified104
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
