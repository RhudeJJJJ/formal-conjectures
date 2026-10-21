/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core030 : Family 6 := level6.get ⟨36,by decide⟩
def sourceMap030 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,7,8,2,3,4,5,6] (sourceLabel 6 0 0 v)
def fusedMap030 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,6,7,8,3,4,5,1,2] (fusedLabel 6 0 0 v)
theorem sourceMap030_checked : acceptsGraphIso
    (source (graph core030) (root 6) 0 0) SmallGeFourSpectrum010.graph
      sourceMap030=true := by decide +kernel
theorem fusedMap030_checked : acceptsGraphIso
    (fused (graph core030) (root 6) 0 0) SmallGeFourSpectrum007.graph
      fusedMap030=true := by decide +kernel
theorem certified030 : Certified (graph core030) (root 6) 0 0 :=
  of_native_maps core030 SmallGeFourSpectrum010.graph SmallGeFourSpectrum007.graph
    sourceMap030 fusedMap030 sourceMap030_checked fusedMap030_checked
    SmallGeFourComparisons.comparison030
#print axioms sourceMap030_checked
#print axioms fusedMap030_checked
#print axioms certified030
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
