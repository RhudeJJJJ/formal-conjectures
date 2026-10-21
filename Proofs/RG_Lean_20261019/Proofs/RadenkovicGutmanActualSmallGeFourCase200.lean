/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core200 : Family 9 := level9.get ⟨599,by decide⟩
def sourceMap200 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap200 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap200_checked : acceptsGraphIso
    (source (graph core200) (root 9) 0 0) SmallGeFourSpectrum211.graph
      sourceMap200=true := by decide +kernel
theorem fusedMap200_checked : acceptsGraphIso
    (fused (graph core200) (root 9) 0 0) SmallGeFourSpectrum145.graph
      fusedMap200=true := by decide +kernel
theorem certified200 : Certified (graph core200) (root 9) 0 0 :=
  of_native_maps core200 SmallGeFourSpectrum211.graph SmallGeFourSpectrum145.graph
    sourceMap200 fusedMap200 sourceMap200_checked fusedMap200_checked
    SmallGeFourComparisons.comparison200
#print axioms sourceMap200_checked
#print axioms fusedMap200_checked
#print axioms certified200
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
