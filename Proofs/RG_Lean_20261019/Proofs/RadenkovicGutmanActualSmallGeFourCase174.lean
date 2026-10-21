/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core174 : Family 9 := level9.get ⟨307,by decide⟩
def sourceMap174 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,8,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap174 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,7,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap174_checked : acceptsGraphIso
    (source (graph core174) (root 9) 0 0) SmallGeFourSpectrum121.graph
      sourceMap174=true := by decide +kernel
theorem fusedMap174_checked : acceptsGraphIso
    (fused (graph core174) (root 9) 0 0) SmallGeFourSpectrum101.graph
      fusedMap174=true := by decide +kernel
theorem certified174 : Certified (graph core174) (root 9) 0 0 :=
  of_native_maps core174 SmallGeFourSpectrum121.graph SmallGeFourSpectrum101.graph
    sourceMap174 fusedMap174 sourceMap174_checked fusedMap174_checked
    SmallGeFourComparisons.comparison174
#print axioms sourceMap174_checked
#print axioms fusedMap174_checked
#print axioms certified174
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
